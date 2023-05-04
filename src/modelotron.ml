(** The point of modelotron is that they come with a composable *)
(** notion of reduction. I am not aware of prior art on this, so I'm *)
(** entitled to choose a silly name for them. The idea is to reduce *)
(** modelotrons to SAT (or, rather, to ∃SAT), so that we can enumerate *)
(** models, count models, and draw random models. *)

module type S = sig

  (** A formula of the modelotron, something that can have a model. *)
  type problem

  (** A refutation of a model, typically, a conjunct for a problem, I
  guess. *)
  type clause

  (** A model of a problem. *)
  type model

  (* In my notes I also have a type of solver, but I think I'll only *)
  (* need it in the full modelotron. *)
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
