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

   Idle thought: this really, really, makes me think of encoding the
   Horn clauses a₁…an→b as a₁…an→▷b (next-g) and the goal g as ⋄g in
   the logic of the topos of trees [ see
   e.g. https://arxiv.org/abs/1208.3596 ]. Except that in the topos of
   trees, you can satisfy this encoding by letting everything be true
   at time 0. So we add these frame rules and initial state which
   prevent this sort of workarounds. I don't know whether we can take
   anything away from that. But I find this interesting. Maybe we can
   see, here, some connection with the encoding of linear logic into a
   (classical) modal logic, by way of a comonadic modality. We are in
   a somewhat dual situation (as ▷ is related to the monadic modality
   ⋄ (specifically, ⋄a = μx.a∨▷x)). *)

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
  | Action of string * int
  | At of 'a * int
  | Selection of 'a

let map_timed f = function
  | Action (s, i) -> Action (s, i)
  | At (a, i) -> At (f a, i)
  | Selection a -> Selection (f a)

let hash h = function
  | Action (name,t) -> CCHash.(combine3 (int 0) (string name) (int t))
  | At (a,t) -> CCHash.(combine3 (int 1) (h a) (int t))
  | Selection a -> CCHash.(combine2 (int 2) (h a))

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
      else Formula.var @@ Selection a

    let action_var (i:int) (name : string) : formula =
      Formula.var @@ Action (name,i)

    let name (i:int) (clause : atom clause) : formula =
      action_var i clause.name

    let steps : int Seq.t = OSeq.(0 --^ P.max_steps)

    let action (i:int) (clause : atom clause) : formula =
      let open Formula in
      name i clause --> ((not (at i clause.concl)) && (conj_map (at i) clause.hyps) && at (i+1) clause.concl)

    let frames (i:int) : formula Seq.t =
      let one_frame (i:int) (a:atom) : formula =
        let open Formula in
        let changed = not (at i a) && at (i+1) a in
        let must_activate =
          disj_map_seq (action_var i) (StringSet.to_seq (M.find a P.timed))
        in
        changed--> must_activate
      in
      M.to_seq P.timed |> Seq.map fst |> Seq.map (one_frame i)

    let monotonicity (i:int) : formula Seq.t =
      let one_monotonicity (i:int) (a:atom) : formula =
        let open Formula in
        at i a --> at (i+1) a
      in
      M.to_seq P.timed |> Seq.map fst |> Seq.map (one_monotonicity i)

    let maximalisation (i:int) (c:atom clause) : formula =
      Formula.((conj_map (at i) c.hyps && not (at i c.concl))--> name i c)
  end

  let convert (prog : atom program) : formula Seq.t =
    let _ = Logs.debug (fun m -> m "%i@." (List.length prog.clauses)) in
    let add_add a n m =
      let upd = function
        | None -> Some (StringSet.singleton n)
        | Some s -> Some (StringSet.add n s)
      in
      M.update a upd m
    in
    let timed =
      (* XXX: make sure the goal is timed. *)
      List.fold_left (fun acc c -> add_add c.concl c.name acc) M.empty (prog.clauses)
    in
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
    let steps : int Seq.t = OSeq.(0 --^ max_steps) in
    let r =
    OSeq.flatten @@ OSeq.of_list [
      OSeq.return initial_state;
      OSeq.return goal;
      begin
        let open OSeq in
        steps >>= fun i ->
          OSeq.append
            begin List.to_seq prog.clauses >>= fun c ->
              OSeq.of_list [
                L.maximalisation i c;
                L.action i c;
              ]
            end
            begin
              OSeq.append
                (L.monotonicity i)
                (L.frames i)
            end
      end;
    ]
    in
    let _ = Logs.debug (fun m -> m "Done converting@.") in
    r

end
