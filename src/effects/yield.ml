[@@@alert "-unstable"]

module type Type = sig
  type t
end

module Make (T: Type) = struct

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

  (* Passed to continuation to discard them cleanly. *)
  exception Unwind

  (* Unrolls a continuation while respecting the invariant that the
     continuation must be consumed. *)
  let discard r =
    let open Effect.Shallow in
    let rec unwind : 'a 'b. ('a, 'b) continuation -> unit = fun k ->
        begin
          try
            discontinue_with
              k
              Unwind
              {
                retc = (fun _ -> ());
                exnc = raise;
                effc = fun(type a) (eff : a Effect.t) ->
                  match eff with
                  | Yield _ -> Some begin fun (k : (a, _) continuation) -> unwind k end
                  | _ -> None
              }
          with
            | _ -> ()
        end
    in
    unwind !r

  let to_gen seq =
    let open Effect.Shallow in
    let state = ref (fiber seq) in
    (* Makes it possible to freely forget the gen *)
    let () = Gc.finalise discard state in
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

  let to_seq gen = OSeq.of_gen (to_gen gen)
end
