(** A small library on using algebraic effects to write
     generators. Algebraic effects are not stabilised, to the library
     is kept small in order to easily deal with updates in the
     future. *)

[@@@alert "-unstable"]

module type Type = sig
  type t
end

(** The @Yield@ effect is parameterised by an arbitrary type. Due to
    effects needing to be monomorphic this parameterisation is done
    via a functor. It looks a bit silly for @Yield@, but I anticipate
    that many effects would require more structure of their
    parameters, and will need to be functors so it's quite uniform
    this way.

    The library is voluntarily (and probably necessarily)
    impoverished: if you need more composition you'll want to convert
    to a more composable form (Seq/Gen/Iter). *)
module Make: functor (T: Type) -> sig
    (** Type of algebraic-effect based generators. They produce values
      with [yield], suspending their computations, and are resumed
      with algebraic handler. The return type is a value returned
      after all the values have been yielded. *)
    type 'a t = unit -> 'a

    val yield : T.t -> unit

    val fold_left : ('a -> T.t -> 'a) -> 'a -> (unit -> 'b) -> 'a * 'b

    val iter : (T.t -> unit) -> (unit -> 'a) -> 'a

    val to_iter : (unit -> unit) -> (T.t -> unit) -> unit

    (** Absolutely not thread safe. *)
    val to_gen : (unit -> unit) -> unit -> T.t option

    val to_seq : (unit -> unit) -> T.t Seq.t

    (** Be careful about using handlers directly, as they require the
    unstable Effect API. *)
    module Handler: sig

      val fold_left :
        ('a -> T.t -> 'a) -> 'a -> ('b, 'a * 'b) Effect.Shallow.handler
      val iter : (T.t -> unit) -> ('a, 'a) Effect.Deep.handler
    end
  end
