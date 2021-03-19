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
module Env = Map.Make (struct type t = declaration let compare = Stdlib.compare end)

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
    atoms : atom list;
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
    | Bottom of int (* int is the arity *)
    | Inter of expr * expr (* Same arity*)
    | Union of expr * expr (* Same arity*)
    | Cross of expr * expr
    | Same of int * int * expr (* both indices in range *)
    | EqAtom of int * atom * expr (* index in bound *)
    | Proj of int list * expr (* all indices in range *)

  type formula =
    | ExistsSome of expr  (* the relation is non-empty *)


  type binding = {
    var: declaration;
    rhs: expr;
  }

  type prog = {
      atoms: atom list;
      instance: declaration list;
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
  (* XXX: maybe we don't want to use Formula, actually but bdds
    directly. *)
  type rel = satvar Formula.t Rel.t

  type env = rel Env.t

  let rec tuples : atom list -> int -> atom list Iter.t = fun atoms arity ->
    if arity <= 0 then Iter.singleton []
    else
      let open Iter in
      tuples atoms (arity-1) >>= fun tuple ->
      List.to_iter atoms >>= fun a ->
      return (a :: tuple)

  (* XXX: should really be in the `Rel` module (and the current `Rel`
  module shouldn't actually be named that, or exposed for that matter)*)
  let of_iter : (atom list * satvar Formula.t) Iter.t -> rel = fun pairs ->
    let not_false = function (_, Formula.Zero) -> false | _ -> true in
    let combine : satvar Formula.t -> satvar Formula.t option -> satvar Formula.t option
      = fun f -> function
      | None -> Some f
      | Some f' -> Some Formula.( f' || f )
    in
    let of_iter_disj kvs =
      let m = ref Rel.empty in
      kvs (fun (k, v) -> m := Rel.update k (combine v) !m);
      !m
    in
    of_iter_disj (Iter.filter not_false pairs)

  (* TODO: Right now, the instance relations are fully unconstrained,
     so they are basically a full matrix together with a boolean value
     per cell. We are going to get a lot of mileage in the future by
     restricting the possible variables /a priori/. A good way to
     obtain such restriction is with types. *)
  (* TODO: can I keep a reverse mapping var -> tuple*declaration so
    that I can print meaningful feedback? *)
  let init_instance : atom list -> declaration list -> env =
    let new_var =
      let c = ref 0 in
      fun () ->
        let r = !c in
        incr c;
        r
    in
    fun atoms decls ->
      let init_decl : declaration -> declaration * rel = fun decl ->
        let new_rel =
          of_iter begin
              tuples atoms (decl.arity)
              |> Iter.map (fun tuple -> (tuple, Formula.Var (new_var ())))
            end
        in
        (decl, new_rel)
      in
      decls
      |> List.to_iter
      |> Iter.map init_decl
      |> Env.of_iter

  (* XXX: note that union and intersection below, to preserve the
    invariants that all keys have the same length need to apply to
    relations with the same arity. It would probably be healthy to do
    a pass of arity checking on relation expressions before compiling
    them. *)

  let rec compile_expr : atom list -> env -> expr -> rel = fun atoms env e ->
    match e with
    | Var r -> Env.find r env
    | Top arity -> of_iter (Iter.map (fun tuple -> (tuple, Formula.one)) (tuples atoms arity))
    | Bottom _arity -> Rel.empty
    | Inter (r1, r2) ->
       Rel.merge_safe
         (compile_expr atoms env r1)
         (compile_expr atoms env r2)
         ~f:begin fun _ -> function
              | `Left _ | `Right _ -> None
              | `Both (f1,f2) -> Some Formula.( f1 && f2 )
                                      (* XXX: this could be zero*)
         end
    | Union (r1, r2) ->
       Rel.merge_safe
         (compile_expr atoms env r1)
         (compile_expr atoms env r2)
         ~f:begin fun _ -> function
              | `Left f1 -> Some f1
              | `Right f2 -> Some f2
              | `Both (f1,f2) -> Some Formula.( f1 || f2 )
         end
    | Cross (r1, r2) ->
       of_iter begin
           let open Iter in
           (compile_expr atoms env r1 |> Rel.to_iter) >>= fun (tuple1, f1) ->
           (compile_expr atoms env r2 |> Rel.to_iter) >>= fun (tuple2, f2) ->
           return (tuple1 @ tuple2, Formula.( f1 && f2 ))
         end
    | Same (i1, i2, r) ->
       of_iter begin
           Iter.filter
             (fun (tuple, _) -> String.equal (List.nth tuple i1) (List.nth tuple i2))
             (compile_expr atoms env r |> Rel.to_iter)
         end
    | EqAtom (i, a, r) ->
       of_iter begin
           Iter.filter
             (fun (tuple, _) -> String.equal (List.nth tuple i) a)
             (compile_expr atoms env r |> Rel.to_iter)
         end
    | Proj (is, r) ->
       of_iter begin
           compile_expr atoms env r
           |> Rel.to_iter
           |> Iter.map (fun (tuple, f) -> (List.map (List.nth tuple) is, f))
          end

  let compile_formula : atom list -> env -> formula -> satvar Formula.t = fun atoms env f ->
     match f with
     | ExistsSome r ->
        compile_expr atoms env r
        |> Rel.to_iter
        |> Iter.map snd
        |> Iter.fold Formula.(||) Formula.Zero

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

let deref : declaration -> RelAlg.expr Env.t -> RelAlg.expr = fun d env ->
  (* Assumption: either a relation is an instance relation, or, it's
     defined in the environment *)
  Env.get_or d env ~default:(Var d)

(* TODOs:
- Handle the case where there are atoms in the head of the rule
- Handle recursion *)
let compile_rule : RelAlg.expr Env.t -> rule -> RelAlg.expr = fun env r ->
  (* A rule looks like this R(x, y) :- S(y), T(x, a)
   * - We first transform it to Top/2 × S × T
   * - Then apply Same/EqAtom corresponding to the variable/atom
   *   arguments of S and T.
   * - Finally, we project on the first two columns *)
  let n = rule_arity r in
  let pre_rhs = RelAlg.(Cross (Top n, List.fold_left (fun acc l ->
                                          Cross(acc, deref (l.root) env)) (Top 0) r.rhs)) in
  let offsets = CCList.scan_left (fun o l -> o + l.root.arity) n r.rhs in
  let offseted = CCList.combine_shortest offsets r.rhs in
  let pos x = index_of (Stdlib.(=) (Var x)) (r.head.arguments) in
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

let compile_rules : rule list -> RelAlg.expr Env.t -> RelAlg.expr Env.t = fun rs env ->
  let grouped =
    CCList.group_by
      ~hash:(fun r -> Hashtbl.hash r.head.root)
      ~eq:(fun r1 r2 -> Stdlib.(r1.head.root = r2.head.root))
      rs
  in
  List.map
    begin fun ds ->
      (* Where [ds] is the list of all the rules whose head is a
         given symbol *)
      (List.hd ds).head.root,
      let compiled = List.map (compile_rule env) ds in
      List.fold_left (fun r1 r2 -> RelAlg.Union (r1, r2)) (List.hd compiled) (List.tl compiled)
    end
    grouped
    |> Env.of_list

let compile_and_inflate_rules : rule list -> RelAlg.expr Env.t -> RelAlg.expr Env.t = fun rs env ->
  Env.union (fun _ e' e -> Some (RelAlg.Union (e', e)))
    (compile_rules rs env) env

let get_derived : prog -> declaration list = fun prog ->
  let add_ds : declaration list -> rule -> declaration list = fun acc r ->
    r.head.root :: List.map (fun l -> l.root) r.rhs @ acc
  in
  prog.rules |> List.fold_left add_ds [] |> List.filter (fun d -> not (List.mem d prog.instance))

let lattice_height : prog -> int = fun prog ->
  let get_decl_height : declaration -> int = fun d ->
    Int.pow (List.length prog.atoms) d.arity
  in
  prog |> get_derived |> List.map get_decl_height |> List.fold_left (+) 0

let bottom_env : prog -> RelAlg.expr Env.t = fun prog ->
  prog |> get_derived
  |> List.map (fun d -> (d, RelAlg.Bottom d.arity)) |> Env.of_list

(* TODOs:
- Handle existentially quantified variables in goal. (current idea,
 * handle the existentially quantified variable like the defined
 * relation for rules. That is, add the Top relation of the arity
 * (here number of existentially quantified variables). And use
 * similar stuff)
- Can we factor the initial bit with compile_rule?*)
let compile_goal : RelAlg.expr Env.t -> literal list -> RelAlg.formula = fun env g ->
  let n = 0 in
  let pre_constr = RelAlg.(Cross (Top n, List.fold_left (fun acc l ->
                                             Cross(acc, deref (l.root) env
                                           )) (Top 0) g)) in
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
  RelAlg.ExistsSome (filtered_constr)

let compile_prog : prog -> RelAlg.prog = fun prog ->
  { RelAlg.instance = prog.instance;
    atoms = prog.atoms;
    constr = compile_goal (Fun.iterate (lattice_height prog) (compile_and_inflate_rules prog.rules) (bottom_env prog)) prog.goal
  }

(* This is an intermediate step, where the notion of program stays
 * the same as pre-datalog. So that we can debug. But the spirit is
 * that we will define more general programs where the instance
 * relations are defined in the text. *)
let interp_rando_program : Types.program -> prog = fun p ->
  let open Types in
  (* XXX: we are ignoring multiplicity *)
  let assigned = { name = "∈"; arity = 2 } in
  let have =  { name = "have"; arity = 1 } in
  let reach =  { name = "reach"; arity = 1 } in
  (* XXX: Assuming, here, that atoms and location don't share names,
     which they actually may, I suppose. *)
  let atoms = p.locations @ List.map fst p.pool in
  let instance = [assigned] in
  let interp_atom : (MultipliedItem.t, Empty.t
                    ) Atom.t -> literal = fun a ->
    match a with
    | Types.Atom.Reach l -> { root = reach ; arguments = [Atom l]}
    (* XXX: ignoring the index (for multiple copies) *)
    | Types.Atom.Have (it, _) -> { root = have ; arguments = [Atom it]}
    | Types.Atom.Assign (_, nothing) -> Empty.absurd nothing
  in
  let interp_clause = fun c ->
    { head = interp_atom c.Clause.goal ;
      rhs = List.map interp_atom c.requires }
  in
  let rules =
    (* have: x <- x ∈ l, reach l *)
    let have_def =
      { head = { root = have ; arguments = [Var "x"] } ;
        rhs = [{ root = assigned ; arguments = [Var "l"; Var "x"] };
               { root = reach ; arguments = [Var "l"] }]
      }
    in
    have_def :: List.map interp_clause p.logic
  in
  let goal = [interp_atom p.goal] in
  { atoms; instance; rules; goal }

(*  LocalWords:  arity datalog
 *)
