(** The point of modelotron is that they come with a composable
    notion of reduction. I am not aware of prior art on this, so I'm
    entitled to choose a silly name for them. The idea is to reduce
    modelotrons to SAT (or, rather, to ∃SAT), so that we can enumerate
    models, count models, and draw random models.

    We reduce to ∃SAT because it's the natural place for drawing
    random models.

    The form of the reduction is really looks like a lens. There is
    prior work in using lens-like structures to compose
    transformations. See {{:
    https://link.springer.com/chapter/10.1007/978-3-642-37036-6_2} The
    Compiler Forest} where the lens-like structure is called Milner
    tactics, and represent compiler passes. *)

module type S = sig

  (** A formula of the modelotron, something that can have a model. *)
  type problem

  (** A refutation of a model, typically, a conjunct for a problem, I
      guess. *)
  type clause

  (** A model of a problem. *)
  type model

  (* In my notes I also have a type of solver, but I think I'll only
     need it in the full modelotron / model counter. *)
end

module type Reduction = sig
  module M: S
  module R: S

  type read_back =
    | Model of M.model
    | Refutation of R.clause

  (** For model counting and random generation it is important that
      each model of the original problem is the read-back of exactly
      one model of the reducts's problem. *)
  type reduced = {
    interpreted: R.problem;
    read_back: R.model -> read_back
  }

  val reduce : M.problem -> reduced

  (** This is use for composition of read_backs. It does feel a little
      ad hoc, but it seems unavoidable. *)
  val translate : M.clause -> R.clause
end

module Compose (Red1: Reduction) (Red2: Reduction with module M = Red1.R) : Reduction with module M = Red1.M and module R = Red2.R = struct
  module M = Red1.M
  module R = Red2.R

  type read_back =
    | Model of M.model
    | Refutation of R.clause

  type reduced = {
    interpreted: R.problem;
    read_back: R.model -> read_back
  }

  let convert_read_back1 : Red1.read_back -> read_back = function
    | Red1.Model model -> Model model
    | Red1.Refutation clause1 -> Refutation (Red2.translate clause1)

  let reduce prob =
    let reduced1 = Red1.reduce prob in
    let reduced2 = Red2.reduce reduced1.interpreted in
    {
      interpreted = reduced2.interpreted;
      read_back = begin
        fun model2 ->
          match reduced2.read_back model2 with
          | Red2.Model model1 -> convert_read_back1 (reduced1.read_back model1)
          | Red2.Refutation clause2 -> Refutation clause2
      end;
    }

  let translate clause2 = Red2.translate (Red1.translate clause2)
end

(* The experiment below doesn't look particularly fruitful. *)
(* type ('m, 'r) reduction = (module Reduction with *)
(* type M.problem = 'mp *)
(* and type M.clause = 'mc *)
(* and type M.model = 'mm *)
(* and type R.problem = 'rp *)
(* and type R.model = 'rp *)
(* and type R.clause = 'rc) *)
(* constraint 'm = < problem: 'mp; clause: 'mc; model: 'mm > *)
(* constraint 'r = < problem: 'rp; clause: 'rc; model: 'rm > *)

(* let (<.>) (type m) (type r) (type t): (m, r) reduction -> (r, t) reduction *)
(*             -> ('m,'t) reduction = fun (module R1) (module R2)-> *)

(* XXX: duplicated from multiplicity.ml *)
module type Literal = sig

  type t

  include Msat__.Solver_intf.FORMULA with type t := t

  val fresh : unit -> t

  (* XXX: Maybe what I really want is finitely supported functions of
     sorts. But I'll deal with maps explicitly for the time being. *)
  module Map: Map.S with type key = t
end

(** ∃SAT, like SAT, but only tracks a subset of the variables (the
    other ones are existentially quantified). Part of the point is
    that the Tseitin transform is model-preserving in ∃SAT. *)
module type EXSAT = sig

  module Literal: Literal

  type problem = { observed: unit Literal.Map.t; clauses: Literal.t list list }

  (** only allowed to refer to observed variables. *)
  type clause = Literal.t list

  (** Solver's state *)
  type t

  val create : problem -> t
  val refuteWith : clause -> t -> unit

  (* An atom can be assigned to true, to false, or unassigned, in
     which case it's irrelevant to the model. *)
  type model = bool Literal.Map.t

  val find : t -> model option

  (** Clause which refutes the model. *)
  val refutation_clause : model -> clause
end

module EXSatSolver (L: Literal) : EXSAT with module Literal = L = struct
  module Interface = struct
    module Formula = L
    type proof = unit
  end

  module Sat = Msat.Make_pure_sat(Interface)

  module Literal = L

  type problem = { observed: unit Literal.Map.t; clauses: Literal.t list list }

  type clause = Literal.t list

  type t = { observed: unit Literal.Map.t; state: Sat.t }

  let create { observed; clauses } =
    let state = Sat.create () in
    let () = Sat.assume state clauses () in
    { observed; state }

  let refuteWith clause { state; _ } = Sat.assume state [clause] ()

  type model = bool Literal.Map.t

  let find { observed; state } : model option =
    match Sat.solve state with
    | Sat.Sat sat ->
      let s =
        let open OSeq in
        let+ (observed_atom, ()) = Literal.Map.to_seq observed in
        try
          let v = sat.eval observed_atom in
          let _ = Logs.debug (fun m -> m "observe: %a=%b@." L.pp observed_atom v) in
          Some (observed_atom, v)
        with
          | Sat.UndecidedLit ->
            let _ = Logs.debug (fun m -> m "observe: %a undecided@." L.pp observed_atom) in
            None
      in
      Some (Literal.Map.of_seq @@ OSeq.filter_map Fun.id s)
    | Sat.Unsat _ -> None

  let refutation_clause model : clause =
    let open OSeq in
    List.of_seq
    @@ let+ (atom, v) = Literal.Map.to_seq model in
    match v with
    | true -> atom
    | false -> Literal.neg atom
end

module type ModelCounter = sig

  type problem

  type model

  val enumerate : problem -> model OSeq.t

  (* I suspect that due to the combinatorial aspects of our problem,
     we are likely to have more than 2^64 models. In this case, of
     course, exact_model_count will never return; but it's worth using
     the same time for exact_model_count and its approximate
     variants. So I may want to use some big integer type. *)
  val exact_model_count : problem -> int

  (* TODO: is there a natural ZDD that we could produce to summarise all the models? *)
end

module MakeModelCounter (Solver: EXSAT) (R: Reduction with module R = Solver) = struct

  type problem = R.M.problem

  type model = R.M.model

  let enumerate prob =
    let R.{ interpreted; read_back } = R.reduce prob in
    let solver = Solver.create interpreted in
    let rec find_m_model : unit -> (R.R.model * R.M.model) option = fun () ->
        let open CCOption in
        let* proposal = Solver.find solver in
        match read_back proposal with
        | Model model -> Some (proposal, model)
        | Refutation clause ->
          let () = Solver.refuteWith clause solver in
          find_m_model ()
    in
    OSeq.of_gen
      begin
        fun () ->
          let open CCOption in
          let* (a_r_model, a_m_model) = find_m_model () in
          let () = Solver.refuteWith (Solver.refutation_clause a_r_model) solver in
          Some a_m_model
      end

  let exact_model_count prob = OSeq.length (enumerate prob)
end

module FirstOrder (A: Literal) = struct
  type problem = A.t Formula.t
  type clause = A.t list
  type model = bool A.Map.t
end

module Tseitin (A: Literal) (Solver: EXSAT with module Literal = A) : Reduction with module M = FirstOrder (A) and module R = Solver = struct

  module M = FirstOrder(A)
  module R = Solver

  type read_back =
    | Model of M.model
    | Refutation of R.clause

  type reduced = {
    interpreted: R.problem;
    read_back: R.model -> read_back
  }

  module MSatTseitin = Msat_tseitin.Make(A)

  (* Let me use effects sparingly. As Ocaml kindly warns me that the
     API for effect is expected to change in the future. I think this
     one use-case serves as a nice demonstration, though. *)
  type _ Effect.t += Observe : A.t -> unit Effect.t
  let observe atom : unit = Effect.perform (Observe atom)

  let reduce (formula : M.problem) =
    let union _ _ _ = Some () in
    let rec interpreted0 =
      let open MSatTseitin in
      function
      | Formula.One -> make_or []
      | Formula.Zero -> make_and []
      | Formula.Var atom -> let () = observe atom in make_atom atom
      | Formula.And (r, l) -> make_and [interpreted0 r; interpreted0 l]
      | Formula.Or (r, l) -> make_or [interpreted0 r; interpreted0 l]
      | Formula.Not f -> make_not (interpreted0 f)
      | Formula.Impl (r, l) -> make_imply (interpreted0 r) (interpreted0 l)
    in
    let interpreted1 formula =
      let open Effect.Shallow in
      let gather =
        let rec gatherOn observed =
          {
            retc = (fun x -> (observed, x));
            exnc = raise;
            effc = fun(type a) (eff : a Effect.t) ->
              match eff with
              | Observe atom ->
                Some
                  begin
                    fun (k : (a, _) continuation) ->
                      continue_with k () (gatherOn (A.Map.add atom () observed))
                  end
              | _ -> None
          }
        in
        gatherOn A.Map.empty
      in
      continue_with (fiber interpreted0) formula gather
    in
    let interpreted =
      let (observed, clauses0) = interpreted1 formula in
      let clauses = MSatTseitin.make_cnf clauses0 in
      Solver.{ observed; clauses }
    in
    let read_back model = Model model in
    { interpreted; read_back }

  let translate clause = clause
end
