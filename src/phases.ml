(* The goal of this file is to define a notion of phase into which we
   want to divide our pipeline into. Specifically, we want things like
   the provability transformation or the multiplicity transformation
   to be passes.

   Really, a pass has two phase:
   - It first transform the problem into a new problem
   - Then it transforms the solution to the new problem into a solution to the original problem

   Some people noticed [citation needed], in the context of compilers, that this was exactly the same thing as Milner's tactics do. Except with a slightly more general type.goal

   orig_prob -> (new_prob, new_solution -> orig_solution)

   This happens to be the same thing as lenses (like in Haskell's lens library). Which suggests an interesting twist: it is now common to use the equivalent, yet somewhat easier to handle type forall f. Functor f => (new_prob -> f new_solution) -> (orig_prob -> f orig_solution). *)

open Types

(* module type Functor = sig
 *
 *   type 'a t
 *
 *   val map : ('a -> 'b) -> 'a t -> 'b t
 *
 * end
 *
 * module type Pass = functor (F:Functor) -> sig
 *
 *   type prob
 *   type sol
 *   type sub
 *   type partial
 *
 *   val run : (sub -> partial F.t) -> (prob -> sol F.t)
 *
 * end
 *
 * type ('prob,'sol,'sub,'partial) pass = (module Pass with type prob='prob type sol='sol) *)

type ('prob,'sol,'sub,'partial) pass = 'prob -> ('sub * ('partial->'sol))

let ( *>) : 's 't 'u 'v 'a 'b. ('s,'t,'u,'v) pass -> ('u,'v,'a,'b) pass -> ('s,'t,'a,'b) pass = fun p1 p2 prob ->
  let (sub1, sol1) = p1 prob in
  let (sub2, sol2) = p2 sub1 in
  (sub2, fun partial2 -> sol1 (sol2 partial2))

let ( ** ) : 's 't 'u 'v 'a 'b 'c 'd. ('s,'t,'a,'b) pass -> ('u,'v,'c,'d) pass -> ('s*'u,'t*'v,'a*'c,'b*'d) pass = fun pl pr (probl, probr) ->
  let (subl, soll) = pl probl in
  let (subr, solr) = pr probr in
  ((subl, subr), fun (partiall,partialr) -> (soll partiall, solr partialr))

let run : 'prob 'sol 'a. ('prob, 'sol, 'a, 'a) pass -> 'prob -> 'sol = fun p prob ->
  let (sub, sol) = p prob in
  sol sub



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

module Make (P:CompileArg) = struct


  let indexed (i:Item.t) : IndexedItem.t Seq.t =
    let open OSeq in
    let n = List.assoc i P.the_program.pool in
    (0 --^ n) >>= fun j ->
    return @@ IndexedItem.make i j


  module LiteralsWithMults = struct
    include TimedIndexedLiteral
    type u = TimedLiteral.t

    let norm_u = TimedLiteral.norm

    let decomp ((neg,l) : u) : (t list * int)=
      let decomp_atom = function
        | Atom.Have (MultipliedOrIndexed.Left (i,k)) ->
          let individualised =
            List.of_seq begin
              let open OSeq in
              indexed i >>= fun ii ->
              return @@ Atom.Have ii
            end
          in
          (individualised, k)
        | a -> ([Atom.map (function MultipliedOrIndexed.Left _ -> assert false | Right i -> i) (fun i -> i) a], 1)
      in
      let decomp_timed_atom = function
        | Provable.Action (s, i) -> [Provable.Action (s,i)], 1
        | Provable.At (a, i) ->
          let (individualised, k) = decomp_atom a in
          List.map (fun b -> Provable.At(b,i)) individualised, k
        | Provable.Selection a ->
          let (individualised, k) = decomp_atom a in
          List.map (fun b -> Provable.Selection b) individualised, k
      in
      let (invidualised, k) = decomp_timed_atom l in
      List.map (fun a -> (neg,a)) invidualised, k
  end
  module Mult = Multiplicity.Make(LiteralsWithMults)



  let to_provable : type a.
    ( program
    , a
    , ((MultipliedOrIndexed.t, IndexedItem.t) Atom.t Provable.program
      * ((MultipliedOrIndexed.t, IndexedItem.t) Atom.t->bool))
    , a)
    pass = fun prog ->

    let gen_rule_name : unit -> string =
      let count = ref 0 in
      fun () ->
        let r = "Rule " ^ string_of_int (!count) in
        incr count;
        r
    in

    let clause (c : Clause.t) : (MultipliedOrIndexed.t, IndexedItem.t) Atom.t Provable.clause =let open Provable in
      let open Clause in
      let cast = Atom.map (fun i-> MultipliedOrIndexed.Left i) (Empty.absurd) in
      {
        hyps=List.map cast c.requires;
        concl= cast c.goal;
        name=gen_rule_name ()
      }
    in

    let logic_clauses = List.map clause prog.logic in

    let assign_clauses =
      List.of_seq begin
        let open OSeq in
        List.to_seq prog.pool >>= fun (i,_) ->
        indexed i >>= fun ii ->
        List.to_seq prog.locations >>= fun l ->
        return begin
          let open Provable in {
              hyps = [ Atom.Reach l; Atom.Assign(l,ii) ];
              concl = Atom.Have (MultipliedOrIndexed.Right ii);
              name = gen_rule_name ()
          }
        end
      end
    in

    ({
        clauses = logic_clauses @ assign_clauses;
        goal =
          let convert_multiple = function
            | (i,1) -> MultipliedOrIndexed.Right (IndexedItem.make i 0)
            (* XXX: it's actually incorrect if there are several copies of i. *)
            | _ -> failwith "TODO: goals with multiplicities"
          in
          Atom.map convert_multiple Empty.absurd prog.goal
      }, (function Atom.Assign _ -> true | _ -> false)),

    fun x -> x



  module Prove = Provable.Make(IndexedAssignmentAtom.Map)

  let convertProvable : type a.
    ( (MultipliedOrIndexed.t, IndexedItem.t) Atom.t Provable.program
      * ((MultipliedOrIndexed.t, IndexedItem.t) Atom.t->bool)
    , a
    , Prove.atom Provable.timed Formula.t Seq.t
    , a)
    pass = fun (prog, selection) ->

    Prove.convert prog selection,

    fun x -> x


  let accrueAssignConstraint : type a.
    ( Prove.atom Provable.timed Formula.t Seq.t
    , a
    , Prove.atom Provable.timed Formula.t Seq.t
    , a)
    pass = fun proof_system ->

    let assign (i : IndexedItem.t) (l : Location.t) : formula =
      Formula.var (Provable.Selection (Atom.Assign(l,i)))
    in
    let range (p : program) (r : RangeConstraint.t) : formula =
      let at_least = Formula.conj_map_seq begin fun i ->
          Formula.disj_map (fun l -> assign i l) r.range
        end (indexed r.scrutinee)
      in
      (* XXX: consider generating at_most/only constraint independently
         from the range, on _all_ locations. *)
      let at_most =
        let ordered_pairs_of_locations =
          let open OSeq in
          begin
            List.to_seq r.range >>= fun l ->
            List.to_seq r.range >>= fun l' ->
            return (l,l')
          end |>
          Seq.filter (fun (l,l') -> Location.compare l l' < 0)
        in
        (* Careful: these are largely order while the above are strictly ordered. *)
        let ordered_pairs_of_items =
          let open OSeq in
          begin
            indexed r.scrutinee >>= fun i ->
            indexed r.scrutinee >>= fun i' ->
            return (i,i')
          end |>
          Seq.filter (fun (i,i') -> IndexedItem.compare i i' <= 0)
        in
        let open Formula in
        conj_seq begin
          let open OSeq in
          ordered_pairs_of_items >>= fun (i,i') ->
          ordered_pairs_of_locations >>= fun (l,l') ->
          return @@ not (assign i l' && assign i' l)
        end
      in
      let only =
        let other_locations =
          List.to_seq p.locations |>
          OSeq.filter (fun l -> not (List.mem l r.range))
        in
        let open Formula in
        let open OSeq in
        conj_seq begin
          indexed r.scrutinee >>= fun i ->
          other_locations >>= fun l ->
          return @@ not (assign i l)
        end
      in
      Formula.(at_least && at_most && only)
    in
    let ranges_formula = Seq.map (range P.the_program) (List.to_seq P.the_program.range_constraints) in
    let capacity (p : program) (l : Location.t) : formula =
      let distinct_pairs =
        let all_items =
          List.to_seq p.pool
          |> Seq.flat_map (fun (i,_) -> indexed i)
        in
        begin
          let open OSeq in
          all_items >>= fun i ->
          all_items >>= fun i' ->
          return (i, i')
        end |>
        Seq.filter (fun (i,i') -> not (IndexedItem.equal i i'))
      in
      let open Formula in
      conj_map (fun (i,i') -> not (assign i l && assign i' l)) (List.of_seq distinct_pairs)
      (* XXX: There is probably a bug here: these are defined in terms
         of items, I'm pretty sure they should be defined in terms of
         indexed_items. *)
    in
    let capacities_formula = Seq.map (capacity P.the_program) (List.to_seq P.the_program.locations)
    in

    OSeq.flatten @@ OSeq.of_list
      [ ranges_formula;
        capacities_formula;
        proof_system
      ],

    fun x -> x

  (* XXX: everywhere: Prove.atom Provable.timed is TimedAtom.t. *)
  let adjoinObservables : type a.
    ( Prove.atom Provable.timed Formula.t Seq.t
    , a
    , Prove.atom Provable.timed Formula.t Seq.t * Prove.atom Provable.timed array
    , a)
    pass = fun formulas ->

    let observables =
      OSeq.(formulas >>= Formula.vars)
      |> TimedAtom.Set.of_seq
      |> TimedAtom.Set.to_seq
      |> OSeq.filter (fun a -> match a with Provable.Selection (Atom.Assign _) -> true | _ -> false)
      |> Array.of_seq
    in

    (formulas, observables),
    fun x -> x

  let convertToCnf : type a.
    ( Prove.atom Provable.timed Formula.t Seq.t
    , a
    , TimedLiteral.t list Seq.t
    , a)
    pass = fun formulas ->

    formulas |> OSeq.flat_map TimedLiteral.cnf_seq,
    fun x -> x

  let observablesToLiterals  : type a.
    ( Prove.atom Provable.timed array
    , a
    , TimedLiteral.t array
    , a)
    pass = fun observables ->

    observables
    |> Array.map TimedLiteral.of_atom ,
    fun x -> x


  let compileMult : type a.
    ( TimedLiteral.t list Seq.t
    , a
    , Mult.atom list list
    , a)
    pass = fun clauses ->

    Mult.compile (List.of_seq clauses),
    fun x -> x

  let indexObservables : type a.
    ( TimedLiteral.t array
    , a
    , Mult.atom array
    , a)
    pass = fun observables ->

    observables
    |> Array.map (fun (neg,l) -> (neg, Provable.map_timed (Atom.map (fun _ -> assert false) (fun i -> i)) l))
    |> Array.map (fun a -> Mult.Individual a) ,
    fun x -> x

end
