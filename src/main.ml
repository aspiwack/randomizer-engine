(* Context:
- we have a bunch of items, and a (larger) bunch of locations.
- Reaching a location requires some objects, we have to achieve a goal
- objects can be restricted to a subset of locations.

Design objectives:
- Have a notion of program that describes valid states.
- Compile it to an efficient form
- Be able to sample a valid state with uniform probability

Steps:
- Design a data type for programs
- Compile program to bdd (standard form, from a library)
- Export bdd to dot, for inspection
- Translate bdd to an samplable representation (probably zdd)
- Implement example sampler
- Parse programs
*)

open Types
let (&&&) = MLBDD.dand
let (|||) = MLBDD.dor
let anot = MLBDD.dnot
let (-->) = MLBDD.imply

module MultipliedOrIndexed = Either(MultipliedItem)(IndexedItem)
type formula = (MultipliedOrIndexed.t, IndexedItem.t) Atom.t Provable.timed Formula.t


module IndexedAssignmentAtom = Atom.Make(MultipliedOrIndexed)(IndexedItem)
module TimedAtom = Provable.MakeTimed(IndexedAssignmentAtom)
module TimedLiteral = Sat.Literal(TimedAtom)

module TimedIndexedAtom = Provable.MakeTimed(Atom.Make(IndexedItem)(IndexedItem))
module TimedIndexedLiteral = Sat.Literal(TimedIndexedAtom)
module TimedLiteralMap = Map.Make(TimedLiteral)

module type CompileArg = sig

  val the_program : program

end

module Compile (P : CompileArg) = struct

  module Phase = Phases.Make(P)

  let pipeline =
    let open Phases in
    let open Phase in
    to_provable
    *> convertProvable
    *> accrueAssignConstraint
    *> adjoinObservables
    *> (convertToCnf ** observablesToLiterals)
    *> (compileMult ** indexObservables)

  let invert_array (arr : Phase.Mult.L.t array) : int Phase.Mult.L.Map.t =
    Array.to_seqi arr |>
    Seq.fold_left (fun acc (i,a) -> Phase.Mult.L.Map.add a i acc) Phase.Mult.L.Map.empty

  let compile_formula man var_index (f : Phase.Mult.L.t Formula.t) : MLBDD.t =
    let mk_var (l : Phase.Mult.L.t) : MLBDD.t =
      match Phase.Mult.L.norm l with
      | (a, Msat.Negated) -> MLBDD.dnot @@ MLBDD.ithvar man (Phase.Mult.L.Map.find a var_index)
      | (a, Msat.Same_sign) -> MLBDD.ithvar man (Phase.Mult.L.Map.find a var_index)
    in
    let rec compile = let open Formula in function
        | Zero -> MLBDD.dfalse man
        | One -> MLBDD.dtrue man
        | Var l -> mk_var l
        | And (x,y) -> compile x &&& compile y
        | Or (x,y) -> compile x ||| compile y
        | Impl (x,y) -> MLBDD.imply (compile x) (compile y)
        | Not x -> anot (compile x)
    in
    compile f

  module Solver = Sat.Solver(Phase.Mult.L)(Phase.Mult.L.Map)

  let to_bdd (p : program) : (MLBDD.t * Phase.Mult.L.t array) =
    let (clauses, observable) = Phases.run pipeline p in
    let var_index = invert_array observable in
    let man = MLBDD.init () in
    let solver = Solver.create () in
    let _ = Solver.assume_clauses solver (List.to_seq clauses) in
    Solver.successive_formulas solver observable
    |> Seq.map (compile_formula man var_index)
    |> OSeq.fold (|||) (MLBDD.dfalse man)
  , observable

  let femto_example =
    let open Clause in
    (* A bit of early Alltp logic *)
    (* items *)
    let sword = "Sword"
    (* locations *)
    and well = "Karakiko Well"
    and eastern_boss = "Eastern Boss"
    in
    let pool = List.map (fun i -> (i,1)) [sword] in
    let locations = [well; eastern_boss; ] in
    let goal = Atom.Reach eastern_boss in
    let range_constraints = [
      {RangeConstraint.scrutinee=sword; range=locations};
    ] in
    let logic = [
      {goal=Reach eastern_boss; requires=[Have (sword, 1)]};
      {goal=Reach well; requires=[]};
    ] in
    { locations; pool; range_constraints; range_definitions=StringMap.empty; logic; goal }

  let micro_example =
    let open Clause in
    (* A bit of early Alltp logic *)
    (* items *)
    let sword = "Sword"
    and bow = "Bow"
    (* locations *)
    and well = "Karakiko Well"
    and hideout = "Blind's Hideout"
    and eastern_chest = "Eastern Small Chest"
    and eastern_boss = "Eastern Boss"
    in
    let pool = List.map (fun i -> (i,1)) [sword; bow] in
    let locations = [well; hideout; eastern_chest; eastern_boss; ] in
    let goal = Atom.Reach eastern_boss in
    let range_constraints = [
      {RangeConstraint.scrutinee=sword; range=locations};
      {RangeConstraint.scrutinee=bow; range=locations};
    ] in
    let logic = [
      {goal=Reach eastern_boss; requires=[Have (bow, 1); Have (sword, 1)]};
      {goal=Reach well; requires=[]};
      {goal=Reach hideout; requires=[]};
      {goal=Reach eastern_chest; requires=[]};
    ] in
    { locations; pool; range_constraints; range_definitions=StringMap.empty; logic; goal }

  let mini_example =
    let open Clause in
    (* A bit of early Alltp logic *)
    (* items *)
    let sword = "Sword"
    and bow = "Bow"
    and eastern_big = "Eastern Big Key"
    (* locations *)
    and well = "Karakiko Well"
    and hideout = "Blind's Hideout"
    and eastern_chest = "Eastern Small Chest"
    and eastern_big_chest = "Easter Big Chest"
    and eastern_boss = "Eastern Boss"
    in
    let pool = List.map (fun i -> (i,1)) [sword; bow; eastern_big] in
    let locations = [well; hideout; eastern_chest; eastern_big_chest; eastern_boss; ] in
    let eastern_palace = [eastern_chest; eastern_big_chest; eastern_boss] in
    let goal = Atom.Reach eastern_boss in
    let range_constraints = [
      {RangeConstraint.scrutinee=sword; range=locations};
      {RangeConstraint.scrutinee=bow; range=locations};
      {RangeConstraint.scrutinee=eastern_big; range=eastern_palace};
    ] in
    let logic = [
      {goal=Reach eastern_boss; requires=[Have (bow, 1); Have (sword, 1); Have (eastern_big, 1)]};
      {goal=Reach well; requires=[]};
      {goal=Reach hideout; requires=[]};
      {goal=Reach eastern_chest; requires=[Have (eastern_big, 1)]};
      {goal=Reach eastern_big_chest; requires=[]};
    ] in
    { locations; pool; range_constraints; range_definitions=StringMap.empty; logic; goal }

  let example =
    let open Clause in
    (* A bit of early Alltp logic *)
    (* items *)
    let sword = "Sword"
    and bow = "Bow"
    and boots = "Boots"
    and glove = "Power Glove"
    and eastern_big = "Eastern Big Key"
    and desert_big = "Desert Big Key"
    (* locations *)
    and well = "Karakiko Well"
    and hideout = "Blind's Hideout"
    and eastern_chest = "Eastern Small Chest"
    and eastern_big_chest = "Easter Big Chest"
    and eastern_boss = "Eastern Boss"
    and desert_torch = "Desert Torch"
    and desert_big_chest = "Desert Big Chest"
    and desert_boss = "Desert Boss"
    in
    let pool = List.map (fun i -> (i,1)) [sword; bow; boots; glove; eastern_big; desert_big] in
    let locations = [well; hideout; eastern_chest; eastern_big_chest; eastern_boss; desert_torch; desert_big_chest; desert_boss] in
    let eastern_palace = [eastern_chest; eastern_big_chest; eastern_boss] in
    let desert_palace = [desert_torch; desert_big_chest; desert_boss] in
    let goal = Atom.Reach desert_boss in
    let range_constraints = [
      {RangeConstraint.scrutinee=sword; range=locations};
      {RangeConstraint.scrutinee=bow; range=locations};
      {RangeConstraint.scrutinee=boots; range=locations};
      {RangeConstraint.scrutinee=glove; range=locations};
      {RangeConstraint.scrutinee=eastern_big; range=eastern_palace};
      {RangeConstraint.scrutinee=desert_big; range=desert_palace};
    ] in
    let logic = [
      {goal=Reach eastern_boss; requires=[Have (bow, 1); Have (sword, 1); Have (eastern_big, 1)]};
      {goal=Reach desert_boss; requires=[Have (glove, 1); Have (sword, 1); Have (eastern_big, 1)]};
      {goal=Reach desert_torch; requires=[Have (boots, 1)]};
      {goal=Reach well; requires=[]};
      {goal=Reach hideout; requires=[]};
      {goal=Reach eastern_chest; requires=[]};
      {goal=Reach eastern_big_chest; requires=[Have (eastern_big, 1)]};
      {goal=Reach desert_big_chest; requires=[Have (desert_big, 1)]};
    ] in
    { locations; pool; range_constraints; range_definitions=StringMap.empty; logic; goal }

  let print_to_dot legend b ~file =
    (* Adapted from Jean-Christophe Filliâtre's bdd library*)
    let open Format in
    let module H1 = Hashtbl.Make(struct type t = MLBDD.t let equal = MLBDD.equal let hash = MLBDD.hash end) in
    let c = open_out file in
    let fmt = formatter_of_out_channel c in
    fprintf fmt "digraph bdd {@\n";
    let visited = H1.create 1024 in
    let rec visit b =
      if not (H1.mem visited b) then begin
        H1.add visited b ();
        match MLBDD.inspectb b with
        | BFalse ->
          fprintf fmt "%d [shape=box label=\"0\"];" (MLBDD.id b)
        | BTrue ->
          fprintf fmt "%d [shape=box label=\"1\"];" (MLBDD.id b)
        | BIf (l, v, h) ->
          (* add_rank v b; *)
          fprintf fmt "%d [label=\"x%a\"];" (MLBDD.id b) (Provable.pp_timed_atom Item.pp) (legend.(v-1));
          fprintf fmt "%d -> %d;@\n" (MLBDD.id b) (MLBDD.id h);
          fprintf fmt "%d -> %d [style=\"dashed\"];@\n" (MLBDD.id b) (MLBDD.id l);
          visit h; visit l
      end
    in
    visit b;
    fprintf fmt "}@.";
    close_out c

end

let parse_file (filename : String.t) =
  let chan = open_in filename in
  let lexbuf = Sedlexing.Utf8.from_channel chan in
  let supplier () =
    let tok = Lexer.tokenise lexbuf in
    let (startp, endp) = Sedlexing.lexing_positions lexbuf in
    (tok, startp, endp)
  in
  let starting_point = Parser.Incremental.program (fst (Sedlexing.lexing_positions lexbuf)) in
  let interp_range_expression prog = function
    | Grammar.RangeLiteral locs -> locs
    | Grammar.RangeIdent id -> StringMap.find id prog.range_definitions
  in
  let accumulate_range prog = function
    | Grammar.RangeDecl (item, range_expr) ->
      let locs = interp_range_expression prog range_expr in
      let range = {RangeConstraint.scrutinee=item; range=locs} in
      { prog with
        pool = (item, 1) :: prog.pool;
        locations = locs @ prog.locations;
        range_constraints = range :: prog.range_constraints;
      }
    | Grammar.RangeDef (ident, range_expr) ->
      let locs = interp_range_expression prog range_expr in
      { prog with
        range_definitions = StringMap.add ident locs prog.range_definitions;
      }
  in
  let convert_atom = function
    | Grammar.Have item -> Atom.Have(item, 1)
    | Grammar.Reach loc -> Atom.Reach loc
  in
  let accumulate_rule prog (goal, requires) =
    let clause =
      let open Clause in
      { goal = convert_atom goal;
        requires = List.map convert_atom requires;
      }
    in
    { prog with
      logic = clause :: prog.logic;
    }
  in
  (* XXX: we shouldn't need to uniquise the location, instead we
     should have an authoritative list of locations in the logic
     file. *)
  let uniquise_locations prog =
    let uniquise = CCList.sort_uniq ~cmp:CCString.compare in
    { prog with locations = uniquise prog.locations }
  in
  match Parser.MenhirInterpreter.loop supplier starting_point with
  | sections ->
    let act prog = function
      | Grammar.Ranges rs ->
        List.fold_left accumulate_range prog rs
      | Grammar.Rules rs ->
        List.fold_left accumulate_rule prog rs
      | Grammar.Goal g -> { prog with goal=convert_atom g }
    in
    let raw_program =
      List.fold_left act { goal=(Reach "Dummy land"); pool=[]; locations=[]; range_constraints=[]; range_definitions=StringMap.empty; logic=[] } sections
    in
    let computed_program = uniquise_locations raw_program in
    let _ = Logs.debug (fun m -> m "%a." pp_program computed_program) in
    computed_program
  | exception Grammar.ParseError (Some (startp, endp), msg) -> (* XXX: partial pattern matching!! *)
    let format_pos fmt p =
      let open Lexing in
      Format.fprintf fmt "%i: %i" p.pos_lnum (p.pos_cnum - p.pos_bol)
    in
    (* XXX: Needs to go through the logging thing *)
    let _ = Format.printf "%s: %a — %a@." msg format_pos startp format_pos endp in
    exit 1

let _ =
  let _ = Logs.set_reporter (Logs_fmt.reporter ()) in
  let _ = Logs.set_level (Some Logs.Debug) in
  let example = parse_file "example.logic" in
  let module Comp = Compile(struct let the_program = example end) in
  let (bdd, legend) = Comp.to_bdd example in
  let module Params = struct
    type t = int (* XXX: ints might not be enough *)

    let zero = 0
    let (+) = (+)

    let the_count_for_one = 1

    let pp = CCInt.pp
  end in
  let module Vars = struct
    type t = int

    let the_vars = Array.mapi (fun i _ -> i+1) legend

    let pp fmt i =
      Format.fprintf fmt "%a" Comp.Phase.Mult.L.pp legend.(i)

  end in
  let module Z = Zdd.Make(Params)(Vars) in
  let _ = Logs.debug (fun m -> m "Done producing the bdd. Converting to zdd") in
  let zdd = Z.of_bdd bdd in
  let _ = Logs.debug (fun m -> m "Done converting to zdd. Printing to dot") in
  Z.print_to_dot ~file:"example.dot" zdd
