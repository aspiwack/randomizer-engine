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

end

module PseudoBoolean (A:Literal) = struct

  (* Something like: 2*x + 7*y ⩾ 3 *)
  type clause = {
    linear_combination: (int*A.t) list;
    constant : int
  }

  (* XXX: we need to make sure that all coefficients are positive for
     this to makes in clause_to_bdd. *)
  let sum_of_coefficients (c : clause) : int =
    c.linear_combination
    |> List.to_seq
    |> Seq.map fst
    |> Seq.fold_left (+) 0


  (** [pop_0 c] is the clause obtained from [c] by setting the first
      variable to 0, the variable is also returned
      (normalised). Precondition: [c] is not empty. *)
  let pop_0 (c : clause) : (A.t * clause) =
    match c.linear_combination with
    | (coeff,lit)::lc_rest ->
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
    | (coeff,lit)::lc_rest ->
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
  let clause_to_bdd (c : clause) : A.t array * MLBDD.t =
    let legend =
      c.linear_combination |> List.to_seq |> Seq.map snd |> Array.of_seq
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

  let mk_sat (c : clause) : A.t list list =
    let module Tseitin = Msat_tseitin.Make(A) in
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
    Tseitin.make_cnf @@ MLBDD.foldb mk_node bdd
end


module type AtomsWithMults = sig

  type t
  type u

  (* What is this saying: we want to decompose an multiplied atom into
     its name and its multiplicity. If it's not multiplied (for
     instance because it doesn't make sense to multiply it) then we
     can return 1. Our transformation will make sure, that when
     multiplicity is 1, we don't do arithmetic. *)
  val decomp : t -> (u * int)

  module AtomMap : Map.S with type key = u

  val quantities : int AtomMap.t

end

module Make (A : AtomsWithMults) = struct


  type 'a atoms =
    | Individual of A.u * int
    | Fresh of string * int
    (* The string is some human-entered name, for provenance, and the
       int, is the warranty of freshness. *)

  let fresh =
    (* XXX: it would be better, to have a gen_sym which starts at 0 for
       each different strings. *)
    let gen_sym = ref 0 in
    fun s ->
      let next = !gen_sym in
      let () = incr gen_sym in
      Fresh (s, next)

end
