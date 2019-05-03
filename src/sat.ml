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
    n1 = n2 && A.equal a1 a2

  let hash (n,a) = CCHash.(combine2 (bool n) (A.hash a))

  let pp fmt (n,a) =
    if n then A.pp fmt a
    else Format.fprintf fmt "~%a" A.pp a

  let neg (n,a) = (not n, a)

  let norm ((n,_) as l) =
    if n then (l, Same_sign)
    else (neg l, Negated)

  let one = []
  let zero = [[]]
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

module Solver (A:Atom) (M:Map.S with type key = A.t)= struct

  module Interface = struct
    module Formula = Literal(A)
    type proof = ()
  end

  (* XXX: move lit_to_formula and map_to_formula to Literal, presumably *)
  let lit_to_formula (b,a) =
    if b then Formula.Var a
    else Formula.(not (Var a))

  let map_to_formula m =
    OSeq.fold Formula.(&&) Formula.One begin
      M.to_seq m |> OSeq.map (fun (a,b) -> (b,a)) |> OSeq.map lit_to_formula
    end

  (* Because the module Formula is overridden by the include. *)
  let pp_formula = Formula.pp

  let map_to_and_print_formula m =
    let f = map_to_formula m in
    Format.printf "produce: %a@." (fun fmt f -> pp_formula (fun a fmt -> A.pp fmt a) f fmt) f;
    f

  include Msat.Make_pure_sat(Interface)

  let assume_formulas solver formulas =
    OSeq.iter (fun f ->
        let f' = Interface.Formula.cnf f in
        Format.printf "assume: %a@." (fun fmt f -> pp_formula (fun a fmt -> A.pp fmt a) f fmt) f;
        Format.printf "assume: %a@." (CCList.pp (CCList.pp  ~start:"[" ~stop:"]" Interface.Formula.pp)) f';
        assume solver f' ()) formulas

  let next solver observe =
    match solve solver with
    | Sat sat -> Some begin
        M.of_seq begin
          Array.to_seq observe
          |> OSeq.filter_map begin fun a ->
            try
              let v = sat.eval (true, a) in
              let _ = Format.printf "observe: %a=%b@." A.pp a v in
              Some (a, v)
            with UndecidedLit ->
              let _ = Format.printf "observe: %a undecided@." A.pp a in
              None
          end
        end
      end
    | Unsat _ -> None

  let neg_clause_of_map m =
    List.of_seq begin
      M.to_seq m |> OSeq.map (fun (a,b) -> (not b, a))
    end

  let successive_formulas solver observe =
    OSeq.of_gen begin fun () ->
      CCOpt.map (fun m -> assume solver [neg_clause_of_map m] (); map_to_and_print_formula m) (next solver observe)
    end

end
