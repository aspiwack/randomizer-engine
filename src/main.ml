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
(* Future plan for item: there can be more than one of an item in the
   pool. In which case it will be translated to n variables (where n
   is the number of occurrences of that item in the pool), the
   corresponding range_constraints will be translated to formulas
   which ensure that the n variables are ordered (to avoid generating
   many semantically equal shuffles) *)
type range_constraint = {
  scrutinee: item;
  range: location list }
type atom =
  | Reach of location
  | Have of item
  | Assign of location * item
  (* Assign doesn't come from parsing as it is equivalent to a
     singleton range_constraint. It appears in translations.*)
type clause = {
  goal: atom;
  requires: atom list
}

type program = {
  locations: location list;
  pool: item list;
  range_constraints: range_constraint list;
  logic: clause list;
  goal: atom
}

let print_atom = function
  | Reach l -> "reach: " ^ l
  | Have i -> "have: " ^ i
  | Assign(i,l) -> i ^ " ∈ " ^ l
let print_timed_atom = let open Provable in function
  | Config a -> print_atom a
  | At(a,i) -> print_atom a ^ " @ " ^ string_of_int i
  | Action (n, i) -> n ^ " @ " ^ string_of_int i

let (&&&) = MLBDD.dand
let (|||) = MLBDD.dor
let anot = MLBDD.dnot
let (-->) = MLBDD.imply

(* XXX: do I still need the AtomSet? *)
module AtomSet = Set.Make (struct type t = atom let compare = compare end)
module TimedAtomSet = Set.Make (struct type t = atom Provable.timed let compare = compare end)
module TimedAtomMap = Map.Make (struct type t = atom Provable.timed let compare = compare end)

let invert_array (arr : atom Provable.timed array) : int TimedAtomMap.t =
  Array.to_seqi arr |>
  Seq.fold_left (fun acc (i,a) -> TimedAtomMap.add a (i+1) acc) TimedAtomMap.empty

(* XXX: This uses Bdd.set_max_var which is not at all a safe thing to
   do! If I use the function twice, it will destroy the previous
   bdd. *)
let compile_formula (f : atom Provable.timed Formula.t) : MLBDD.t * atom Provable.timed array =
  let _ = Format.printf "Compiling formula@." in
  let atoms =
    Formula.vars f |> TimedAtomSet.of_seq |> TimedAtomSet.to_seq |> Array.of_seq
  in
  let _ = Format.printf "Done collecting atoms@." in
  let _ = Format.printf "Num atoms: %i@." (Formula.vars f |> OSeq.length) in
  let var_index = invert_array atoms in
  let man = MLBDD.init () in
  let mk_var (a : atom Provable.timed) : MLBDD.t = MLBDD.ithvar man (TimedAtomMap.find a var_index) in
  let rec compile = let open Formula in function
    | Zero -> MLBDD.dfalse man
    | One -> MLBDD.dtrue man
    | Var a -> mk_var a
    | And (x,y) -> compile x &&& compile y
    | Or (x,y) -> compile x ||| compile y
    | Impl (x,y) -> MLBDD.imply (compile x) (compile y)
    | Not x -> anot (compile x)
  in
  let _ = Format.printf "Done compiling formula@." in
  let _ = Format.printf "%t@." (Formula.pp (fun a fmt -> Format.fprintf fmt "%s" (print_timed_atom a)) f) in
  (* assert false *)
  compile f, atoms

let collect_program_atoms (p : program) : AtomSet.t =
  let atoms : atom Seq.t =
    List.to_seq p.pool |>
    Seq.flat_map (fun i ->
      List.to_seq p.locations |>
      Seq.flat_map (fun l -> List.to_seq [Reach l; Have i; Assign(i,l)]))
  in
  AtomSet.of_seq atoms

let gen_rule_name : unit -> string =
  let count = ref 0 in
  fun () ->
    let r = "Rule " ^ string_of_int (!count) in
    incr count;
    r

(* XXX: remove?*)
module AtomMap = Map.Make (struct type t = atom let compare = compare end)

(* XXX: remove?*)
let invert_array (arr : atom array) : int AtomMap.t =
  Array.to_seqi arr |>
  Seq.fold_left (fun acc (i,a) -> AtomMap.add a (i+1) acc) AtomMap.empty

type formula = atom Provable.timed Formula.t

(* XXX: This uses Bdd.set_max_var which is not at all a safe thing to
   do! If I use the function twice, it will destroy the previous
   bdd. *)
let compile_to_bdd (p : program) : (MLBDD.t * atom Provable.timed array) =
  let bdd_vars =
    collect_program_atoms p |> AtomSet.to_seq |> Array.of_seq
  in
  let var_index = invert_array bdd_vars in
  (* let _ = Bdd.set_max_var (Array.length bdd_vars) in *)
  (* let var (a : atom) : formula = Formula.var (AtomMap.find a var_index) in
   * let reach (l : location) : Bdd.t = var (Reach l) in
   * let have (i : item) : Bdd.t = var (Have i) in *)
  let assign (i : item) (l : location) : formula =
    Formula.var (Provable.Config (Assign(i,l)))
  in
  (* XXX: clean *)
  (* let map_reduce (type a) (op : Bdd.t -> Bdd.t -> Bdd.t) (e : Bdd.t) (f : a -> Bdd.t) (l : a list) : Bdd.t =
   *   l |> List.map f |> List.fold_left op e
   * in
   * let conj f l = map_reduce (&&&) Bdd.one f l in
   * let disj f l = map_reduce (|||) Bdd.zero f l in *)
  let clause (c : clause) : atom Provable.clause =
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
  let ranges_formula = Formula.conj_map (range p) p.range_constraints in
  let logic_clauses = List.map clause p.logic in
  let assign_clauses =
    let _ = Format.printf "Creating assign clauses@." in
    let r = List.of_seq begin
      List.to_seq p.pool |>
      Seq.flat_map begin fun i ->
        List.to_seq p.locations |>
        Seq.map begin fun l ->
          let open Provable in {
            hyps = [ Reach l; Assign(i,l) ];
            concl = Have i;
            name = gen_rule_name ()
          }
        end
      end
    end
    in
    let _ = Format.printf "Done creating assign clauses@." in
    r
  in
  let module Prove = Provable.Make(AtomMap) in
  let provable = Prove.convert {
      clauses = logic_clauses @ assign_clauses;
      goal = p.goal
  }
  in
  let _ = Format.printf "really done@." in
  compile_formula begin
    let open Formula in
    ranges_formula && provable (* && goal_formula *)
  end

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
    {goal=Reach eastern_boss; requires=[Have sword]};
    {goal=Reach well; requires=[]};
  ] in
  { locations; pool; range_constraints; logic; goal }

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
    {goal=Reach eastern_boss; requires=[Have bow; Have sword]};
    {goal=Reach well; requires=[]};
    {goal=Reach hideout; requires=[]};
    {goal=Reach eastern_chest; requires=[]};
  ] in
  { locations; pool; range_constraints; logic; goal }

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
    {goal=Reach eastern_boss; requires=[Have bow; Have sword; Have eastern_big]};
    {goal=Reach well; requires=[]};
    {goal=Reach hideout; requires=[]};
    {goal=Reach eastern_chest; requires=[Have eastern_big]};
    {goal=Reach eastern_big_chest; requires=[]};
  ] in
  { locations; pool; range_constraints; logic; goal }

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
    {goal=Reach eastern_boss; requires=[Have bow; Have sword; Have eastern_big]};
    {goal=Reach desert_boss; requires=[Have glove; Have sword; Have eastern_big]};
    {goal=Reach desert_torch; requires=[Have boots]};
    {goal=Reach well; requires=[]};
    {goal=Reach hideout; requires=[]};
    {goal=Reach eastern_chest; requires=[]};
    {goal=Reach eastern_big_chest; requires=[Have eastern_big]};
    {goal=Reach desert_big_chest; requires=[Have desert_big]};
  ] in
  { locations; pool; range_constraints; logic; goal }

let print_to_dot b ~file =
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
            fprintf fmt "%d [label=\"x%d\"];" (MLBDD.id b) v;
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

let _ =
  let (bdd, legend) = compile_to_bdd femto_example in
  let _ =
    Array.to_seqi legend |>
    Seq.iter (fun (i,v) -> Format.printf "x%i: %s@." (i+1) (print_timed_atom v))
  in
  Format.printf "%b@." (MLBDD.is_false bdd);
  (* print_string @@ MLBDD.to_stringb bdd *)
  print_to_dot ~file:"example.dot" bdd
