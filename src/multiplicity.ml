(*

  So we have at this point formulas for the form

  "PoD small key" * 7 ∈ { … } reach: "PoD right chest" :- have: 2*"PoD
   small key", have: Bow

  We can transform the clause into a new formula:

  reach: "PoD right chest" :- (have: "PoD small key"_0 + have: "PoD
   small key"_1 + have: "PoD small key"_2 + have: "PoD small key"_3 +
   have: "PoD small key"_4 + have: "PoD small key"_5 + have: "PoD
   small key"_6 ⩾ 2), have: Bow

  However, this is not a clause that we can interpret. It's neither
   CNF, nor is it a pseudo-boolean clause like in the minisat+ paper [
   http://minisat.se/downloads/MiniSat+.pdf ]

  We can introduce a new variable `f`, such that `f` stands for the
   pseudo-boolean constraint, to be solved.

  reach: "PoD right chest" :- f, have: Bow

  f∨(have: "PoD small key"_0 + have: "PoD small key"_1 + have: "PoD
   small key"_2 + have: "PoD small key"_3 + have: "PoD small key"_4 +
   have: "PoD small key"_5 + have: "PoD small key"_6 < 2*¬f)

  Alternative encoding

  have: "PoD small key"_0 + have: "PoD small key"_1 + have: "PoD small
   key"_2 + have: "PoD small key"_3 + have: "PoD small key"_4 + have:
   "PoD small key"_5 + have: "PoD small key"_6 < 2*¬f + M*f (here M is
   7)

  If I didn't say nonsense, the models (up to the value of `f`) are
   the same. *)

module type Literal = sig

  type t

  include Msat__.Solver_intf.FORMULA with type t := t

  val fresh : unit -> t

  (* XXX: Maybe what I really want is finitely supported functions of
     sorts. But I'll deal with maps explicitly for the time being. *)
  module Map : Map.S with type key = t

end

module PseudoBoolean (A:Literal) = struct

  type scaled = S of int * A.t
    (* Internal. Invariant: the coefficient is always strictly positive. *)

  let coefficient = fun (S(coeff, _)) -> coeff
  let variable = fun (S(_, var)) -> var

  let mk_scaled i l =
    if i > 0 then Some(0, S(i,l))
    else if i < 0 then Some(i, S(-i, A.neg l)) (* we replace `x` by `1 - ¬x` *)
    else (* if i=0 *) None

  (* Something like: 2*x + 7*y ⩾ 3 *)
  type clause = {
    linear_combination: scaled list;
    constant : int
  }

  module Expr = struct

    type t = int A.Map.t * int
    (* Invariant: all the keys are “normalised” (that is there is a
       single key for x and ¬x) *)

    let var l = match A.norm l with
    | (v, Msat__Solver_intf.Same_sign) ->
      ((A.Map.singleton v 1), 0)
    | (v, Msat__Solver_intf.Negated) ->
      ((A.Map.singleton v (-1)), 1) (* ¬x is encoded as (1-x) *)
    let const n = (A.Map.empty, n)
    let m2c = function
      | Some i -> i
      | None -> 0

    let greater_than_or_equal_to_zero (e, n) =
      let (leftover, linear_combination) =
        let module Sum = struct
          type 'a t = int * 'a
          let return x = (0, x)
          let map f (i, x) = (i, f x)
          let (>>=) (i, x) f =
            let (j, y) = f x in
            (i+j, y)
        end in
        let module Summing = OSeq.Traverse(Sum) in
        e |> A.Map.to_seq |> Seq.filter_map (fun (l,i) -> mk_scaled i l) |> Summing.sequence_m |> Sum.map List.of_seq
      in
      let constant = (-n)-leftover in
      { linear_combination; constant }

    let merge_expr ( * ) (e1,n1) (e2,n2) =
      (A.Map.merge (fun _ l r -> Some ((m2c l) * (m2c r))) e1 e2, n1*n2)
    (* Note: I'm not caring too much about 0s here. It should be ok,
       because I never care about equality of exprs. So I let the 0s
       linger around, but I'll remove them when I create a clause. *)

    let (+) e1 e2 = merge_expr (+) e1 e2
    let (-) e1 e2 = merge_expr (-) e1 e2
    let ( * ) k (e,n) = (A.Map.map (fun x -> k*x) e, k*n)

    let (>=) e1 e2 = greater_than_or_equal_to_zero (e1 - e2)
    let (<=) e1 e2 = e2 >= e1
    let (>) e1 e2 = e1 >= (e2 + const 1)
    let (<) e1 e2 = e2 > e1
  end


  let sum_of_coefficients (c : clause) : int =
    c.linear_combination
    |> List.to_seq
    |> Seq.map coefficient
    |> Seq.fold_left (+) 0


  (** [pop_0 c] is the clause obtained from [c] by setting the first
      variable to 0, the variable is also returned
      (normalised). Precondition: [c] is not empty. *)
  let pop_0 (c : clause) : (A.t * clause) =
    match c.linear_combination with
    | S(coeff,lit)::lc_rest ->
      let (var,sign) = A.norm lit in
      begin match sign with
        | Msat__Solver_intf.Negated ->
          (* coeff*¬var + lc_rest ⩾ c.constant *)
          var, { linear_combination = lc_rest; constant = c.constant - coeff }
        | Msat__Solver_intf.Same_sign ->
          (* coeff*var + lc_rest ⩾ c.constant *)
          var, { linear_combination = lc_rest; constant = c.constant }
      end
    | [] -> assert false

  (** [pop_1 c] is the clause obtained from [c] by setting the first
      variable to 1, the variable is also returned
      (normalised). Precondition: [c] is not empty. *)
  let pop_1 (c : clause) : (A.t * clause) =
    match c.linear_combination with
    | S(coeff,lit)::lc_rest ->
      let (var,sign) = A.norm lit in
      begin match sign with
        | Msat__Solver_intf.Negated ->
          (* coeff*¬var + lc_rest ⩾ c.constant *)
          var, { linear_combination = lc_rest; constant = c.constant }
        | Msat__Solver_intf.Same_sign ->
          (* coeff*var + lc_rest ⩾ c.constant *)
          var, { linear_combination = lc_rest; constant = c.constant - coeff }
      end
    | [] -> assert false

  (* I'm just going to do the BDD translation from the minisat+
     paper. If performance becomes an issue, it should be considered
     to look at the other two translations from that same paper. *)

  module IntMap = Map.Make(CCInt)

  (* XXX: return a dictionary to decode the integer variables in the
     bdd, into A.t-s. *)
  (* XXX: The minisat+ gets some extra efficiency out of memoisation. *)
  (* XXX: The minisat+ paper, recommends to pop the variable from the
     one with the bigger coefficient, to the one with the smaller
     coefficient, as it tends to yield smaller BDDs. *)
  let clause_to_bdd (c : clause) : A.t array * MLBDD.t =
    let legend =
      c.linear_combination |> List.to_seq |> Seq.map variable |> Array.of_seq
    in
    let man = MLBDD.init () in
    let rec clause_to_bdd (c : clause) (count : int) : MLBDD.t =
      (* Count is the number of variable which we have already inserted
         in the bdd, it serves as the code of the next variable. *)
      let sum = sum_of_coefficients c in
      if c.constant <= 0 then MLBDD.dtrue man
      else if sum < c.constant then MLBDD.dfalse man
      else
        (* /!\ IMPORTANT: if the length of the clause is 0, then
           sum=0, so we know that c.constant <= 0 && 0 < c.constant
           (by the previous to if-s). It's contradictory, so this
           case never happens. Therefore, the clause has at least one
           variable. *)
        let (_var, fls) = pop_0 c in (* XXX: put var, in an array of sorts. *)
        let (_, tru) = pop_1 c in
        MLBDD.ite (clause_to_bdd fls (count+1)) count (clause_to_bdd tru (count+1))
    in
    (* /!\ It's a bit delicate: we are reconstructing the mapping from
       numbers to variable which was deduced during the loop. Maybe we
       could more robustly pass a reversed index into this to the loop. *)
    legend, clause_to_bdd c 0

  module Tseitin = Msat_tseitin.Make(A)

  let mk_sat (c : clause) : Tseitin.t =
    let mk_ite b t f =
      let open Tseitin in
      let b' = make_atom b in
      make_and [
        make_imply b' t;
        make_imply (make_not b') f
      ]
    in
    let (legend, bdd) = clause_to_bdd c in
    let mk_node = function
      | MLBDD.BFalse -> Tseitin.f_false
      | MLBDD.BTrue -> Tseitin.f_true
      | MLBDD.BIf(f,v,t) -> mk_ite (legend.(v)) f t
    in
    MLBDD.foldb mk_node bdd
end


module type AtomsWithMults = sig

  type t
  type u

  val compare : t -> t -> int

  include Msat.FORMULA with type t := t

  (** What this is saying: we want to decompose an multiplied atom
     into its name and its multiplicity. If it's not multiplied (for
     instance because it doesn't make sense to multiply it) then we
     can return 1. Our transformation will make sure, that when
     multiplicity is 1, we don't do arithmetic.

     The list is all the instances available of the item represented
     by [u].*)
  val decomp : u -> (t list * int)

  val norm_u : u -> u * Msat.Solver_intf.negated

  (* module AtomMap : Map.S with type key = t
   *
   * val quantities : int AtomMap.t *)

end

module Make (A : AtomsWithMults) = struct

  type atom =
    | Individual of A.t
    | Fresh of bool * string * int
    (* The string is some human-entered name, for provenance, and the
       int, is the warranty of freshness.
       Boolean: [false] if negated *)

  let fresh =
    (* XXX: it would be better, to have a gen_sym which starts at 0 for
       each different strings. *)
    let gen_sym = ref 0 in
    fun s ->
      let next = !gen_sym in
      let () = incr gen_sym in
      Fresh (false, s, next)

  module L : Literal with type t = atom = struct

    type t = atom

    let equal a b = match a, b with
      | Individual a, Individual b -> A.equal a b
      | Fresh (na, sa, ia), Fresh (nb, sb, ib) -> na = nb && sa = sb && ia == ib
      | _ -> false

    let hash = function
      | Individual a -> CCHash.(combine2 (int 0) (A.hash a))
      | Fresh (na, sa, ia) -> CCHash.(combine4 (int 1) (bool na) (string sa) (int ia))

    let pp fmt = function
      | Individual a -> A.pp fmt a
      | Fresh (na, sa, ia) ->
        if na then Format.fprintf fmt "f:%s%d" sa ia
        else Format.fprintf fmt "~f:%s%d" sa ia

    let neg = function
      | Individual a -> Individual (A.neg a)
      | Fresh (na, sa, ia) -> Fresh (not na, sa, ia)

    let norm = function
      | Individual a ->
        let (a',n) = A.norm a in
        (Individual a', n)
      | Fresh (na, _, _) as a ->
        if na then (a, Same_sign)
        else (neg a, Negated)

    let fresh () = fresh "m"

    module Map = Map.Make(struct
        type nonrec t = t
        let compare a b = match a, b with
          | Individual a, Individual b -> A.compare a b
          | Individual _, _ -> 1
          | _, Individual _ -> -1
          | Fresh(na, sa, ia), Fresh(nb, sb, ib) ->
            CCOrd.(triple bool string int) (na, sa, ia) (nb, sb, ib)
    end)
  end

  module I = PseudoBoolean(L)

  let compile (p : A.u list list) : atom list list =
    let compile_literal (l : A.u) : I.Tseitin.t =
      let (l, n) = A.norm_u l in
      let restore_negation f = match n with
        | Msat.Negated -> I.Tseitin.make_not f
        | Msat.Same_sign -> f
      in
      let positive =
        match A.decomp l with
        | [single], 1 ->
          I.Tseitin.make_atom (Individual single)
        | individuals, num ->
          let sum = List.fold_left I.Expr.(+) (I.Expr.const 0) in
          I.mk_sat @@
          I.Expr.(sum (List.map (fun i -> var (Individual i)) individuals) >= const num)
      in
      restore_negation positive
    in
    let compile_clause (c : A.u list) : atom list list =
      c
      |> List.map compile_literal
      |> I.Tseitin.make_or
      |> I.Tseitin.make_cnf
    in
    CCList.flat_map compile_clause p

end
