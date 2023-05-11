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
module Make (T: Type) = struct

  (** Type of algebraic-effect based generators. They produce values
      with [yield], suspending their computations, and are resumed
      with algebraic handler. The return type is a value returned
      after all the values have been yielded. *)
  type 'a t = unit -> 'a

  type _ Effect.t += Yield : T.t -> unit Effect.t

  let yield x = Effect.perform @@ Yield x

  module Handler = struct
    (** Be careful about using handlers directly, as they require the
    unstable Effect API. *)

    let rec fold_left f current =
      let open Effect.Shallow in
      {
        retc = (fun x -> (current, x));
        exnc = raise;
        effc = fun(type b) (eff : b Effect.t) ->
          match eff with
          | Yield a ->
            Some
              begin
                fun (k : (b, _) continuation) ->
                  continue_with k () (fold_left f (f current a))
              end
          | _ -> None
      }

    let iter f =
      let open Effect.Deep in
      {
        retc = Fun.id;
        exnc = raise;
        effc = fun(type b) (eff : b Effect.t) ->
          match eff with
          | Yield a ->
            Some
              begin
                fun (k : (b, _) continuation) ->
                  let () = f a in
                  continue k ()
              end
          | _ -> None
      }
  end

  let fold_left f a gen =
    Effect.Shallow.continue_with (Effect.Shallow.fiber gen) () (Handler.fold_left f a)

  let iter f gen =
    Effect.Deep.match_with gen () (Handler.iter f)

  let to_iter gen f = iter f gen

  exception Gen of T.t option

  let to_gen seq =
    let open Effect.Shallow in
    let state = ref (fiber seq) in
    fun () ->
      continue_with
        (!state)
        ()
        {
          retc = (fun () -> None);
          exnc = raise;
          effc = fun(type a) (eff : a Effect.t) ->
            match eff with
            | Yield a ->
              Some
                begin
                  fun (k : (a, _) continuation) ->
                    let () = state := k in
                    Some a
                end
            | _ -> None
        }
end
