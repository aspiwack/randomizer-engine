open Containers

(* Game plan for 2021:

- Generalise the compilation engine (which takes a description of a
   randomizer's logic and returns a sat problem whose models are
   valid/logical shuffles) to compile general datalog programs
   (without negation, which I don't know what we could with)
   - Why? It allows us to define more complex logic.
   - It also cleans up a bit of the code which is very ad hoc, to the
   details of the problem space, and might not generalise beyond the
   logic of alttpr, which I know best.
   - I've got nices of to do it.
   - Tradeoff: may be harder to debug because I don't really know how
   to output proofs.

- I found a way to generate random approximately uniform models of
  sat problems, without relying on an (expensive) compilation step.
  - Also counting (approximately) the number of models (these two
  things are related)
  - The main advantage is that it's going to be much much faster. So
  it will hopefully be quite imaginable to generate custom logics on
  the fly, and draw from them (this can handle things like prefilling
  Ganon's Tower, or multiworld logic).
  - It was not clear that the compilation method was viable for a full
  logic anyway.
*)

(* Datalog game plan:
- Compile datalog to a relational model (following e.g. the method in
  Foundation of Databases)
- Use the method in the Kodkod paper
  https://homes.cs.washington.edu/~emina/pubs/kodkod.tacas07.pdf
  to compile the relation model to SAT.
- Basically, we make it so that database instances in the sense that
  datalog means it (aka facts) are the models of our SAT problem.
- Contrary to Kodkod, we cannot use a symmetry breaking formula: we do
  really want all the models, since at the very least we are counting
  them.
  - However, I believe that symmetry breaking formulae are key to
    encode multiplicities (like having two of the same item,
   e.g. swords in alttpr, of which there are 4)
- We can't model recursion inside SAT. However, we are going to make
  an assumption: there's a finite number of atoms. (in database
  parlance we would say that every column has a finite type)
  - This means that we can bound the number of iteration, and
    translate this into a static problem
- Kodkod notes that because relation composition is associative, you
  can use "fast" exponentiation to compute transitive
  closures. However, I don't think we have anything really
  associative, so our iterations will be much more pedestrian.
*)

(* A datalog program consists of:
- A collection of /instance relation/ declarations, with name and
 arity
- A collection of /declared relation/ declarations, with name and
 arity (maybe implicit)
- A collection of rules whose heads are (built off) declared relations, and rhs
  are lists of instance relations and declared relations (with
  variables, and stuff)
- A goal, which is an existentially quantified conjunction of literals built off instance
  relations and declared relations
*)

(* Common stuff *)
type name = String.t
type var = String.t
type atom = String.t
type declaration = { name: name; arity: int }

type arg =
  | Var of var
  | Atom of atom
type literal = { root: declaration; arguments: arg list }

type rule = {
    head: literal;
    rhs: literal list;
  }

type goal = literal list

type prog = {
    instance: declaration list;
    rules: rule list;
    goal: goal;
  }

module RelAlg = struct
  (* A relation program is
     - A collection of /instance relation/ declarations, with name
       and arities (in the future there will be bounds (e.g. given by
       atom types), which significantly reduce the size of the
       generated sat problem).
     - Definitions of relations (let binders).
     - A constraint, which for simplicity, we will assume, for now, is
       a single relation, and the constraint is that it is non-empty *)

  type expr =
    | Var of declaration
    | Top of int (* int is the arity *)
    | Inter of expr * expr (* Same arity*)
    | Union of expr * expr (* Same arity*)
    | Cross of expr * expr
    | Same of int * int * expr (* both indices in range *)
    | EqAtom of int * atom * expr (* index in bound *)
    | Proj of int list * expr (* all indices in range *)

  type formula =
    | Some of expr  (* the relation is non-empty *)


  type binding = {
    var: declaration;
    rhs: expr;
  }

  type prog = {
      instance: declaration list;
      bindings: binding list;
      constr: formula;
  }

  module Rel = Map.Make(struct type t = atom list let compare = Stdlib.compare end)

  (* TODO: a better name, and abstract compilation over *)
  type satvar = int

  (* The idea:
     - All the keys have length the arity of the relation
     - An absent key means `Zero`

    It's just a finite boolean predicate. Where some values may be
    unknown (crucially!) and will be offloaded to SAT. Then we can see
    which of these values work.

    In the Kodkod paper, they don't use lists of atoms directly but
    encode them as integers. I doubt that it is really useful in
    Ocaml, it's probably an artefact of their implementation
    language. That's my guess anyway.

    TODO(probably): in the Kodkod paper, they represent sequences of
    contiguous `One` as a single interval thingy, rather than a bunch
    of key-value pairs. Since our encoding uses the `Top` relation, we
    can expect such an optimisation to be quite dramatic. But I don't
    really know, yet, how do do this optimisation while keeping the
    implementation complexity reasonable.
     *)
  type rel = satvar Formula.t Rel.t

  module Env = Map.Make (struct type t = declaration let compare = Stdlib.compare end)

  type env = rel Env.t

  let rec tuples : atom list -> int -> atom list Iter.t = fun atoms arity ->
    if arity <= 0 then Iter.singleton []
    else
      tuples atoms (arity-1)
      |> Iter.flat_map (fun tuple -> List.to_iter atoms
      |> Iter.flat_map (fun a -> Iter.singleton (a :: tuple)))

  (* TODO: initialise the environment with values for all the
  /instance/ relations. Right now they are fully unconstrained, so
  they are basically a full matrix together with a boolean value per
  cell. We are going to get a lot of mileage in the future by
  restricting the possible variables /a priori/. A good way to obtain
  such restriction is with types. *)

  let rec compile_expr : atom list -> env -> expr -> rel = fun atoms env e ->
    match e with
    | Var r -> Env.find r env
    | Top arity -> Rel.of_iter (Iter.map (fun tuple -> (tuple, Formula.one)) (tuples atoms arity))
    | Inter (r1, r2) ->
       Rel.merge_safe
         (compile_expr atoms env r1)
         (compile_expr atoms env r2)
         ~f:begin fun _ -> function
              | `Left _ | `Right _ -> None
              | `Both (f1,f2) -> Some Formula.( f1 && f2 )
         end
    | Union (_, _) -> (??)
    | Cross (_, _) -> (??)
    | Same (_, _, _) -> (??)
    | EqAtom (_, _, _) -> (??)
    | Proj (_, _) -> (??)

end

(* We want to
   1/ compile a rule to an expression
   2/ define a bindings for all the rules for the same relation, by
   taking the union of the compilation of these rules. *)

(* TODO: move *)
let rec index_of : ('a -> bool) -> 'a list -> int = fun p l ->
  match l with
  | [] -> assert false
  | x::l -> if p x then 0 else 1 + index_of p l


let rule_arity : rule -> int = fun r ->
  r.head.root.arity

(* TODOs:
- Handle the case where there are atoms in the head of the rule
- Handle recursion *)
let compile_rule : rule -> RelAlg.expr = fun r ->
  (* A rule looks like this R(x, y) :- S(y), T(x, a)
   * - We first transform it to Top/2 × S × T
   * - Then apply Same/EqAtom corresponding to the variable/atom
   *   arguments of S and T.
   * - Finally, we project on the first two columns *)
  let n = rule_arity r in
  let pre_rhs = RelAlg.(Cross (Top n, List.fold_left (fun acc l -> Cross(acc, Var (l.root))) (Top 0) r.rhs)) in
  let offsets = CCList.scan_left (fun o l -> o + l.root.arity) n r.rhs in
  let offseted = CCList.combine_shortest offsets r.rhs in
  let pos x = index_of ((=) (Var x)) (r.head.arguments) in
  let filtered_rhs =
    List.fold_left
      begin fun acc (off,l) ->
        CCList.foldi begin fun inner i arg ->
          match arg with
          | Var x -> RelAlg.Same (off+i, pos x, inner)
          | Atom a -> RelAlg.EqAtom (off+i, a, inner)
        end
        acc l.arguments
      end
      pre_rhs offseted
    in
  RelAlg.Proj (CCList.init n (fun i -> i), filtered_rhs)

let compile_rules : rule list -> RelAlg.binding list = fun rs ->
  let grouped =
    CCList.group_by
      ~hash:(fun r -> Hashtbl.hash r.head.root)
      ~eq:(fun r1 r2 -> r1.head.root = r2.head.root)
      rs
  in
  List.map
    begin fun ds ->
    { RelAlg.var = (List.hd ds).head.root;
      rhs =
        let compiled = List.map compile_rule ds in
        List.fold_left (fun r1 r2 -> RelAlg.Union (r1, r2)) (List.hd compiled) (List.tl compiled)
    }
    end
    grouped

(* TODOs:
- Handle existentially quantified variables in goal. (current idea,
 * handle the existentially quantified variable like the defined
 * relation for rules. That is, add the Top relation of the arity
 * (here number of existentially quantified variables). And use
 * similar stuff)
- Can we factor the initial bit with compile_rule?*)
let compile_goal : literal list -> RelAlg.formula = fun g ->
  let n = 0 in
  let pre_constr = RelAlg.(Cross (Top n, List.fold_left (fun acc l -> Cross(acc, Var (l.root))) (Top 0) g)) in
  let offsets = CCList.scan_left (fun o l -> o + l.root.arity) n g in
  let offseted = CCList.combine_shortest offsets g in
  let filtered_constr =
    List.fold_left
      begin fun acc (off,l) ->
        CCList.foldi begin fun inner i arg ->
          match arg with
          | Var _x -> assert false
          | Atom a -> RelAlg.EqAtom (off+i, a, inner)
        end
        acc l.arguments
      end
      pre_constr offseted
  in
  RelAlg.Some (filtered_constr)




(*  LocalWords:  arity datalog
 *)
