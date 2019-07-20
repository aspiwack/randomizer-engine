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
type variable = string

type location = variable
type item = variable
type indexed_item = item * int
(* Future plan for item: there can be more than one of an item in the
   pool. In which case it will be translated to n variables (where n
   is the number of occurrences of that item in the pool), the
   corresponding range_constraints will be translated to formulas
   which ensure that the n variables are ordered (to avoid generating
   many semantically equal shuffles) *)
type range_constraint = {
  scrutinee: item;
  range: location list }

type 'i atom =
  | Reach of location
  | Have of 'i * int
  | Assign of location * 'i
  (* Assign doesn't come from parsing as it is equivalent to a
     singleton range_constraint. It appears in translations.*)
let map_atom f = function
  | Reach l -> Reach l
  | Have (i, n) -> Have (f i, n)
  | Assign (l, i) -> Assign (l, f i)
type clause = {
  goal: item atom;
  requires: item atom list
}

module StringMap = Map.Make(CCString)

type program = {
  locations: location list;
  pool: item list;
  range_constraints: range_constraint list;
  range_definitions: location list StringMap.t;
  logic: clause list;
  goal: item atom
}

let hash_location = CCHash.string
let hash_item = CCHash.string
let hash_indexed_item (i,n) = CCHash.(combine2 (string i) (int n))
let hash_atom hash_item = function
  | Reach l -> CCHash.(combine2 (int 0) (hash_location l))
  | Have (i, n) -> CCHash.(combine3 (int 1) (hash_item i) (int n))
  | Assign (l,i) -> CCHash.(combine3 (int 2) (hash_location l) (hash_item i))

let print_item i = i
let print_indexed_item (i, n) = i ^ "_" ^ (string_of_int n)
let print_atom print_item = function
  | Reach l -> "reach: " ^ l
  | Have (i,1) -> "have: " ^ print_item i
  | Have (i,n) -> "have: " ^ print_item i ^ " *" ^ (string_of_int n)
  | Assign(l,i) -> print_item i ^ " ∈ " ^ l
let print_timed_atom print_item = let open Provable in function
  | Selection a -> print_atom print_item a
  | At(a,i) -> print_atom print_item a ^ " @ " ^ string_of_int i
  | Action (n, i) -> n ^ " @ " ^ string_of_int i

let pp_clause fmt {goal;requires} =
  let pp_atom fmt a = CCString.pp fmt (print_atom print_item a) in
  Format.fprintf fmt "%a :- @[<hov>%a@]" pp_atom goal (CCList.pp ~sep:"," pp_atom) requires
let pp_range fmt {scrutinee;range} =
  Format.fprintf fmt "%s ∈ {%a}" scrutinee (CCList.pp CCString.pp) range
let pp_program fmt prog =
  (* XXX: I'm not printing range_definitions *)
  let pp_locations = CCList.pp (fun fmt l -> Format.fprintf fmt "@[<h>%s@]" l) in
  let pp_pool = CCList.pp (fun fmt i -> Format.fprintf fmt "@[<h>%s@]" i) in
  let pp_ranges = CCList.pp pp_range in
  let pp_logic = CCList.pp pp_clause in
  let pp_goal fmt g = Format.fprintf fmt "%s." (print_atom print_item g) in
  Format.fprintf fmt "@[<v>@[<v 2>[Locations]@,%a@]@,@[<v 2>[Pool]@,%a@]@,@[<v 2>[Ranges]@,%a@]@,@[<v 2>[Logic]@,%a@]@,@[<v 2>[Goal]@,%a@]@]@." pp_locations prog.locations pp_pool prog.pool pp_ranges prog.range_constraints pp_logic prog.logic pp_goal prog.goal


let (&&&) = MLBDD.dand
let (|||) = MLBDD.dor
let anot = MLBDD.dnot
let (-->) = MLBDD.imply

(* XXX: do I still need the AtomSet? *)
module AtomSet = Set.Make (struct type t = item atom let compare = compare end)
module TimedAtomSet = Set.Make (struct type t = item atom Provable.timed let compare = compare end)
module TimedAtomMap = Map.Make (struct type t = item atom Provable.timed let compare = compare end)
(* XXX: remove?*)
module AtomMap = Map.Make (struct type t = item atom let compare = compare end)

type formula = item atom Provable.timed Formula.t

module TimedLiteral = Sat.Literal(struct type t = item atom Provable.timed let equal = (=) let hash = Provable.hash (hash_atom hash_item) let pp fmt a = Format.fprintf fmt "%s" (print_timed_atom print_item a) end)
module TimedIndexedLiteral = Sat.Literal(struct type t = indexed_item atom Provable.timed let equal = (=) let hash = Provable.hash (hash_atom hash_indexed_item) let pp fmt a = Format.fprintf fmt "%s" (print_timed_atom print_indexed_item a) end)
(* XXX: Literal, should provide its comparison function *)
module TimedLiteralMap = Map.Make(struct type t = TimedLiteral.t let compare = compare end)
module LiteralsWithMults = struct
  include TimedIndexedLiteral
  type u = TimedLiteral.t

  let compare = compare
  let norm_u = TimedLiteral.norm

  let decomp (n,l) =
    ([n,Provable.map_timed (map_atom (fun i -> (i,0))) l], 1)
end
module Mult = Multiplicity.Make(LiteralsWithMults)

let invert_array (arr : Mult.L.t array) : int Mult.L.Map.t =
  Array.to_seqi arr |>
  Seq.fold_left (fun acc (i,a) -> Mult.L.Map.add a i acc) Mult.L.Map.empty

let compile_formula man var_index (f : Mult.L.t Formula.t) : MLBDD.t =
  let mk_var (l : Mult.L.t) : MLBDD.t =
    match Mult.L.norm l with
    | (a, Msat.Negated) -> MLBDD.dnot @@ MLBDD.ithvar man (Mult.L.Map.find a var_index)
    | (a, Msat.Same_sign) -> MLBDD.ithvar man (Mult.L.Map.find a var_index)
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
  (* let _ = Logs.debug (fun m -> m "%t@." (Formula.pp (fun a fmt -> Format.fprintf fmt "%s" (print_timed_atom a)) f)) in *)
  (* assert false *)
  compile f

let collect_program_atoms (p : program) : AtomSet.t =
  let atoms : item atom Seq.t =
    List.to_seq p.pool |>
    Seq.flat_map (fun i ->
      List.to_seq p.locations |>
      Seq.flat_map (fun l -> List.to_seq [Assign(l,i)]))
  in
  AtomSet.of_seq atoms

let gen_rule_name : unit -> string =
  let count = ref 0 in
  fun () ->
    let r = "Rule " ^ string_of_int (!count) in
    incr count;
    r


module Solver = Sat.Solver(Mult.L)(Mult.L.Map)

(* XXX: This uses Bdd.set_max_var which is not at all a safe thing to
   do! If I use the function twice, it will destroy the previous
   bdd. *)
let compile_to_bdd (p : program) : (MLBDD.t * Mult.L.t array) =
  let bdd_vars =
    collect_program_atoms p |> AtomSet.to_seq |> Array.of_seq
  in
  let assign (i : item) (l : location) : formula =
    Formula.var (Provable.Selection (Assign(l,i)))
  in
  let clause (c : clause) : item atom Provable.clause =
    let open Provable in {
      hyps=c.requires;
      concl=c.goal;
      name=gen_rule_name ()
    }
  in
  let range (p : program) (r : range_constraint) : formula =
    let at_least = Formula.disj_map (fun l -> assign r.scrutinee l) r.range in
    (* XXX: consider generating at_most/only constraint independently
       from the range, on _all_ locations. *)
    let at_most =
      let distinct_pairs =
        List.to_seq r.range |>
        Seq.flat_map (fun l -> Seq.map (fun l' -> (l,l')) (List.to_seq r.range)) |>
        Seq.filter (fun (l,l') -> l <> l')
      in
      let open Formula in
      conj_map (fun (l,l') -> not (assign r.scrutinee l && assign r.scrutinee l')) (List.of_seq distinct_pairs)
    in
    let only =
      let other_locations =
        p.locations |>
        List.filter (fun l -> not (List.mem l r.range))
      in
      let open Formula in
      conj_map (fun l -> not (assign r.scrutinee l)) other_locations
    in
    Formula.(at_least && at_most && only)
  in
  let ranges_formula = Seq.map (range p) (List.to_seq p.range_constraints) in
  let capacity (p : program) (l : location) : formula =
    let distinct_pairs =
      List.to_seq p.pool |>
      Seq.flat_map (fun i -> Seq.map (fun i' -> (i, i')) (List.to_seq p.pool)) |>
      Seq.filter (fun (i,i') -> i <> i')
    in
    let open Formula in
    conj_map (fun (i,i') -> not (assign i l && assign i' l)) (List.of_seq distinct_pairs)
  in
  let capacities_formula = Seq.map (capacity p) (List.to_seq p.locations)
  in
  let logic_clauses = List.map clause p.logic in
  let assign_clauses =
    List.of_seq begin
      List.to_seq p.pool |>
      Seq.flat_map begin fun i ->
        List.to_seq p.locations |>
        Seq.map begin fun l ->
          let open Provable in {
            hyps = [ Reach l; Assign(l,i) ];
            concl = Have (i, 1);
            name = gen_rule_name ()
          }
        end
      end
    end
  in
  let module Prove = Provable.Make(AtomMap) in
  let proof_system = Prove.convert {
      clauses = logic_clauses @ assign_clauses;
      goal = p.goal
  }
  in
  let formulas = OSeq.flatten @@ OSeq.of_list
      [ ranges_formula;
        capacities_formula;
        proof_system
      ]
  in
  let clauses = formulas  |> OSeq.flat_map TimedLiteral.cnf_seq in
  let clauses = Mult.compile (List.of_seq clauses) in
  let atoms =
    OSeq.(formulas >>= Formula.vars)
    |> TimedAtomSet.of_seq
    |> TimedAtomSet.to_seq
    |> Array.of_seq
  in
  let observable =
    CCArray.filter (fun a -> match a with Provable.Selection _ -> true | _ -> false) atoms
    |> Array.map (Provable.map_timed (map_atom (fun i -> (i, 0))))
    |> Array.map TimedLiteral.of_atom
    |> Array.map (fun a -> Mult.Individual a)
  in
  let var_index = invert_array observable in
  let man = MLBDD.init () in
  let solver = Solver.create () in
  let _ = Solver.assume_clauses solver (List.to_seq clauses) in
  (* NEXT: change observable to have elements of type Mult.atom. It's really the only way *)
  Solver.successive_formulas solver observable
    |> Seq.map (compile_formula man var_index)
    |> OSeq.fold (|||) (MLBDD.dfalse man)
  , observable

let femto_example =
  (* A bit of early Alltp logic *)
  (* items *)
  let sword = "Sword"
  (* locations *)
  and well = "Karakiko Well"
  and eastern_boss = "Eastern Boss"
  in
  let pool = [sword] in
  let locations = [well; eastern_boss; ] in
  let goal = Reach eastern_boss in
  let range_constraints = [
    {scrutinee=sword; range=locations};
  ] in
  let logic = [
    {goal=Reach eastern_boss; requires=[Have (sword, 1)]};
    {goal=Reach well; requires=[]};
  ] in
  { locations; pool; range_constraints; range_definitions=StringMap.empty; logic; goal }

let micro_example =
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
  let pool = [sword; bow] in
  let locations = [well; hideout; eastern_chest; eastern_boss; ] in
  let goal = Reach eastern_boss in
  let range_constraints = [
    {scrutinee=sword; range=locations};
    {scrutinee=bow; range=locations};
  ] in
  let logic = [
    {goal=Reach eastern_boss; requires=[Have (bow, 1); Have (sword, 1)]};
    {goal=Reach well; requires=[]};
    {goal=Reach hideout; requires=[]};
    {goal=Reach eastern_chest; requires=[]};
  ] in
  { locations; pool; range_constraints; range_definitions=StringMap.empty; logic; goal }

let mini_example =
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
  let pool = [sword; bow; eastern_big] in
  let locations = [well; hideout; eastern_chest; eastern_big_chest; eastern_boss; ] in
  let eastern_palace = [eastern_chest; eastern_big_chest; eastern_boss] in
  let goal = Reach eastern_boss in
  let range_constraints = [
    {scrutinee=sword; range=locations};
    {scrutinee=bow; range=locations};
    {scrutinee=eastern_big; range=eastern_palace};
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
  let pool = [sword; bow; boots; glove; eastern_big; desert_big] in
  let locations = [well; hideout; eastern_chest; eastern_big_chest; eastern_boss; desert_torch; desert_big_chest; desert_boss] in
  let eastern_palace = [eastern_chest; eastern_big_chest; eastern_boss] in
  let desert_palace = [desert_torch; desert_big_chest; desert_boss] in
  let goal = Reach desert_boss in
  let range_constraints = [
    {scrutinee=sword; range=locations};
    {scrutinee=bow; range=locations};
    {scrutinee=boots; range=locations};
    {scrutinee=glove; range=locations};
    {scrutinee=eastern_big; range=eastern_palace};
    {scrutinee=desert_big; range=desert_palace};
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
  (* let ranks = Hashtbl.create 17 in (\* var -> set of nodes *\)
   * let add_rank v b =
   *   try Hashtbl.replace ranks v (S.add b (Hashtbl.find ranks v))
   *   with Not_found -> Hashtbl.add ranks v (S.singleton b)
   * in *)
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
            fprintf fmt "%d [label=\"x%s\"];" (MLBDD.id b) (print_timed_atom print_item (legend.(v-1)));
            fprintf fmt "%d -> %d;@\n" (MLBDD.id b) (MLBDD.id h);
            fprintf fmt "%d -> %d [style=\"dashed\"];@\n" (MLBDD.id b) (MLBDD.id l);
            visit h; visit l
    end
  in
  (* Hashtbl.iter
   *   (fun v s ->
   *      fprintf fmt "{rank=same; ";
   *      S.iter (fun x -> fprintf fmt "%d " x.tag) s;
   *      fprintf fmt ";}@\n"
   *   )
   *   ranks; *)
  visit b;
  fprintf fmt "}@.";
  close_out c

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
      let range = {scrutinee=item; range=locs} in
      { prog with
        pool = item :: prog.pool;
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
    | Grammar.Have item -> Have(item, 1)
    | Grammar.Reach loc -> Reach loc
  in
  let accumulate_rule prog (goal, requires) =
    let clause =
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
  let (bdd, legend) = compile_to_bdd example in
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
      Format.fprintf fmt "%a" Mult.L.pp legend.(i)

  end in
  let module Z = Zdd.Make(Params)(Vars) in
  let _ = Logs.debug (fun m -> m "Done producing the bdd. Converting to zdd") in
  let zdd = Z.of_bdd bdd in
  let _ = Logs.debug (fun m -> m "Done converting to zdd. Printing to dot") in
  Z.print_to_dot ~file:"example.dot" zdd
