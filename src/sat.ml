open Msat.Solver_intf

module type Atom = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val pp : Format.formatter -> t -> unit
end

module Literal (A:Atom) = struct

  (** [A] provides the type of atoms, to make a literal, it is paired
     with a boolean. [true] if the literal is positive, and [false] if
     it's negated. *)
  type t = bool * A.t

  let equal (n1,a1) (n2,a2) =
    n1 == n2 && a1 == a2

  let hash (n,a) = CCHash.(combine2 (bool n) (A.hash a))

  let pp fmt (n,a) =
    if n then A.pp fmt a
    else Format.fprintf fmt "~%a" A.pp a

  let neg (n,a) = (not n, a)

  let norm ((n,_) as l) =
    if n then (l, Same_sign)
    else (neg l, Negated)

  let one = [[]]
  let zero = []
  let (&&) l r = l@r
  let (||) l r =
    List.of_seq begin
      let open OSeq in
      List.to_seq l >>= fun cl ->
      List.to_seq r >>= fun cr ->
      return @@ cl@cr
    end

  (** [cnf] is not, in general, efficient. But it will be given only
     easy cases in practice. In the future, I may avoid cnf altogether
     and produce clauses directly. But since I already have the
     formulas from before, it's less work to cnf them. *)
  let cnf : A.t Formula.t -> t list list =
    let rec cnf n = function
      | Formula.One -> if n then one else zero
      | Formula.Zero -> if n then zero else one
      | Formula.Var a -> [[(n,a)]]
      | Formula.And (l,r) ->
        if n then cnf n l && cnf n r
        else cnf n l || cnf n r
      | Formula.Or (l,r) ->
        if n then cnf n l || cnf n r
        else cnf n l && cnf n r
      | Formula.Not f -> cnf (not n) f
      | Formula.Impl (l,r) -> cnf (not n) l || cnf n r
    in
    cnf true

end

module Solver (A:Atom) = struct

  module Interface = struct
    module Formula = Literal(A)
    type proof = ()
  end

  include Msat.Make_pure_sat(Interface)

  let assume_formulas solver formulas =
    OSeq.iter (fun f -> assume solver (Interface.Formula.cnf f) ()) formulas

end
