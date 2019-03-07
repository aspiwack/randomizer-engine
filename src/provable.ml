(* The goal, in this file, is to take a bunch of Horn clauses and
   assert that a certain goal is provable from the horn clauses. The
   problem is that it does not enjoy a direct encoding into a
   satisfiability problem: if I have {a->b}, it is a model, to say
   that b is 1 and a is 0.

   What we want it build a formula where there are models only if,
   say, b is provable. A first approach would be to make every clause
   into an equivalence (up to some prior grouping). This way {a->b} is
   translated to {a<->b}, which asserts that can't prove {b} without
   first proving {a}. But this is still not sufficient. Indeed, it
   fails if there is any cycle. For instance {b->b} becomes {b<->b},
   so b can be set to 1 in a model. This would happen in randomizer,
   for instance, if you would put a big key in its big chest: the
   formula would then be allowed to consider the big key reachable.

   This is all explained very well, in the context of Answer Set
   Programming, in these slides:
   https://resources.mpi-inf.mpg.de/departments/rg1/conferences/vtsa13/slides/schaub.pdf
   (section Axiomatic Characterization).

   To solve this, we will encode the proving _process_ inside
   satisfiability. To that effect, we are going to encode a state
   evolving through time. Every time we apply a rule, time
   progresses. This is very similar to the solution described in these
   slides:
   http://www.inf.ed.ac.uk/teaching/courses/plan/slides/SAT-Planning-Slides.pdf
   *)

type 'a clause = {
  concl: 'a;
  hyps: 'a list;
  name: string
}

type 'a program = {
  clauses: 'a clause list;
  goal: 'a
}

type 'a timed =
  | Config of 'a
  | Action of string * int
  | At of 'a * int

module StringSet = Set.Make(struct type t=string let compare=compare end)

module Make (M : Map.S) = struct

  type atom = M.key
  type formula = atom timed Formula.t

  (* Translating clauses:
   - Each clause duplicated for each time step. And given a name (actions)
   - Take all the possible actions at each step (maximisation of parallelism)
   - For each clause and each time step, we need to carry the part of the state that is not affected by the clause if it is selected.
   *)

  module type Params = sig
    val timed : StringSet.t M.t
    val max_steps : int
  end

  module MainLoop (P : Params) = struct

    let at (i:int) (a : atom) : formula =
      if M.mem a P.timed then Formula.var @@ At(a,i)
      else Formula.var @@ Config a

    let action (i:int) (name : string) : formula =
      Formula.var @@ Action (name,i)

    let name (i:int) (clause : atom clause) : formula =
      action i clause.name

    let steps : int Seq.t = OSeq.(0 --^ P.max_steps)

    let actions (clauses : atom clause list) : formula =
      let _ = Format.printf "Starting actions@." in
      let one_action (i:int) (clause : atom clause) : formula =
        let open Formula in
        name i clause --> ((not (at i clause.concl)) && (conj_map (at i) clause.hyps) && at (i+1) clause.concl)
      in
      let action (clause : atom clause) : formula =
        Formula.conj_seq begin
          let open OSeq in
          steps >>= fun i ->
          return @@ one_action i clause
        end
      in
      let r = Formula.conj_map action clauses in
      let _ = Format.printf "Done actions@." in
      r

    let frames : formula =
      let _ = Format.printf "Starting frames@." in
      let one_frame (i:int) (a:atom) : formula =
        let open Formula in
        let changed = not (at i a) && at (i+1) a in
        let must_activate =
          disj_map_seq (action i) (StringSet.to_seq (M.find a P.timed))
        in
        changed--> must_activate
      in
      let frame (a:atom) : formula =
        Formula.conj_seq begin
          let open OSeq in
          steps >>= fun i ->
          return @@ one_frame i a
        end
      in
      let r = Formula.conj_seq (M.to_seq P.timed |> Seq.map fst |> Seq.map frame) in
      let _ = Format.printf "Done frames@." in
      r

    let exclusions (clauses : atom clause list) : formula =
      let _ = Format.printf "Starting exclusion@." in
      let actions = List.to_seq clauses |> Seq.map (fun c -> c.name) in
      let distinct_pairs =
        OSeq.product actions actions |> Seq.filter (fun (a,b) -> a <> b)
      in
      let r = Formula.conj_seq begin
        let open OSeq in
        distinct_pairs >>= fun (a, b) ->
        steps >>= fun i ->
        return @@ Formula.(not (action i a && action i b))
      end in
      let _ = Format.printf "Done exclusions@." in
      r

    let maximalisations (clauses : atom clause list) : formula =
      let one_maximalisation (i:int) (c:atom clause) : formula =
        Formula.((conj_map (at i) c.hyps && not (at i c.concl))--> name i c)
      in
      let maximalisation (c:atom clause) : formula =
        Formula.conj_seq begin
          let open OSeq in
          steps >>= fun i ->
          return @@ one_maximalisation i c
        end
      in
      Formula.conj_map maximalisation clauses

  end

  let convert (prog : atom program) : formula =
    let _ = Format.printf "%i@." (List.length prog.clauses) in
    let add_add a n m =
      let upd = function
        | None -> Some (StringSet.singleton n)
        | Some s -> Some (StringSet.add n s)
      in
      M.update a upd m
    in
    let timed =
      List.fold_left (fun acc c -> add_add c.concl c.name acc) M.empty (prog.clauses)
    in
    (* Idea of improvement: only allow rules to apply when they change
       something. It would presumably reduce the search space, hence
       the BDD. *)
    let max_steps = List.length (prog.clauses) in
    let module L = MainLoop (struct let timed=timed let max_steps=max_steps end) in
    let initial_state =
      Formula.conj_seq begin
        M.to_seq timed
        |> Seq.map fst
        |> Seq.map (fun a -> Formula.(not (var (At(a,0)))))
      end
    in
    let goal =
      Formula.disj_seq begin
        let open OSeq in
        0--max_steps >>= fun i ->
        return @@ Formula.var (At(prog.goal,i))
      end
    in
    let open Formula in
    let r =
    initial_state
    && goal
    && L.frames
    && L.maximalisations (prog.clauses)
    (* && L.exclusions (prog.clauses) *)
    && L.actions (prog.clauses)
    in
    let _ = Format.printf "Done converting@." in
    r

end
