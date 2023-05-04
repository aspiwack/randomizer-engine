(*

 What we really need is a _path-counting_ ZDD*.

 Definition: each node is annotated with the number of paths to One.

 We are going to consider a slight generalisation: a monoid-caching ZDD.

 We have
 - a commutative (additive) monoid
 - The zero-node of our ZDD has weight 0
 - The one-node has some fixed weight
 - Variables nodes have, as their weight, the sum of the weight of their subnodes.

*)

open Hashcons

module type Param = sig

  type t

  val zero : t
  val ( + ): t -> t -> t
  (* XXX: be parametric on the equality and hash function. Maybe. *)

  val the_count_for_one : t

  val pp : Format.formatter -> t -> unit
end

module type Var = sig

  type t = int

  val the_vars : t array

  val pp : Format.formatter -> t -> unit
end

module Make (P: Param) (V: Var) = struct

  let the_vars =
    let my_vars = Array.copy V.the_vars in
    let _ = Array.sort compare my_vars in
    my_vars

  module Core = struct
    type t = node hash_consed
    and node =
      | Zero
      | One
      | If of { var: V.t; no: t; yes: t; count: P.t }

    module Node = struct
      type t = node

      let equal n1 n2 =
        match n1, n2 with
        | Zero, Zero -> true
        | One, One -> true
        | If{ var = var1; no = no1; yes = yes1; _ }, If{ var = var2; no = no2; yes = yes2; _ } ->
          var1 = var2 && no1.tag = no2.tag && yes1.tag = yes2.tag
        | _ -> false

      let hash = function
        | Zero -> CCHash.int 0
        | One -> CCHash.int 1
        | If{ var; no; yes; _ } -> CCHash.(combine4 (int 2) (int var) no.hkey yes.hkey)
    end

    module H = Hashcons.Make(Node)
    (* GLOBAL EFFECT!! *)
    let the_table : H.t = H.create 42

    let count_node = function
      | Zero -> P.zero
      | One -> P.the_count_for_one
      | If{ count; _ } -> count

    let equal (b1 : t) (b2 : t) : bool =
      b1.tag = b2.tag

    let hash (b : t) : int =
      b.hkey

    let count_t { node; _ } = count_node node

    let pp_node fmt = function
      | Zero -> Format.fprintf fmt "zero"
      | One -> Format.fprintf fmt "one"
      | If{ var; _ } -> Format.fprintf fmt "%d" var

    let mk node = H.hashcons the_table node

    let zero = mk Zero

    (* Careful, this can only be internal, as it doesn't necessarily
     respect the ordering of variables. *)
    let mkIf (no : t) (var : V.t) (yes : t) : t =
      if equal yes zero then
        no
      else
        let count = P.(count_t no + count_t yes) in
        mk (If { var; no; yes; count })

    let one =
      Array.fold_right (fun var child -> mkIf child var child) the_vars (mk One)

    let of_bool = function
      | false -> zero
      | true -> one

    let rec app (op : bool -> bool -> bool) (b1 : t) (b2 : t) : t =
      app_node op (b1.node, b2.node)
    and app_node op = function
      | Zero, Zero -> of_bool @@ op false false
      | Zero, One -> of_bool @@ op false true
      | One, Zero -> of_bool @@ op true false
      | One, One -> of_bool @@ op true true
      | Zero, If{ var; no; yes; _ } -> Format.printf "1@."; mkIf (app op zero no) var (app op zero yes)
      | If{ var; no; yes; _ }, Zero -> Format.printf "2@."; mkIf (app op no zero) var (app op yes zero)
      | One, If{ var; no; yes; _ } -> Format.printf "3@."; mkIf (app op one no) var (app op zero yes)
      | If{ var; no; yes; _ }, One -> Format.printf "4@."; mkIf (app op no one) var (app op yes zero)
      | If{ var = varl; no = nol; yes = yesl; _ }, If{ var = varr; no = nor; yes = yesr; _ } when varl = varr ->
        Format.printf "6: %d %d %d %d %d@." varl nol.tag yesl.tag nor.tag yesr.tag; mkIf (app op nol nor) varl (app op yesl yesr)
      | If{ var = varl; _ } as left, If{ var; no; yes; _ } when varl > var ->
        Format.printf "7@."; mkIf (app_node op (left, no.node)) var (app op zero yes)
      | If{ var; no; yes; _ }, right (* when varr > var *) ->
        Format.printf "8@."; mkIf (app_node op (no.node, right)) var (app op yes zero)

    let var v =
      let if_or_v var child =
        if var = v then
          mkIf zero var child
        else
          mkIf child var child
      in
      let _ = Format.printf "start var@." in
      let _ = Format.printf "%a@." (CCArray.pp CCInt.pp) the_vars in
      let res = Array.fold_right if_or_v the_vars (mk One) in
      let _ = Format.printf "end var@." in
      res

    let not_var v =
      let if_or_v var child =
        if var = v then
          child
        else
          mkIf child var child
      in
      let _ = Format.printf "start not_var@." in
      let res = Array.fold_right if_or_v the_vars (mk One) in
      let _ = Format.printf "end not_var@." in
      res

    let if_ b1 v b2 =
      let impl = app (fun x y -> not x || y) in
      let band = app ( && ) in
      let _ = Format.printf "start if_" in
      let res = band (impl (not_var v) b1) (impl (var v) b2) in
      let _ = Format.printf "end if_" in
      res
  end

  include Core

  (* Of note: here I assume that `the_vars` is actually indexed by the
    number that the bdd uses. I'm creating a zdd with the same
    variable names (integers) as the bdd, but since the zdd has its
    variable names fixed, it must be a superset of those used by the
    bdd. *)
  let of_bdd (b : MLBDD.t) : t =
    let module Input = struct
      type t = int * MLBDD.t
      let equal (i1, b1) (i2, b2) = i1 = i2 && MLBDD.equal b1 b2
      let hash (i, b) = CCHash.(combine2 (int i) (MLBDD.hash b))
    end in
    let module H1 = Hashtbl.Make(Input) in
    let visited = H1.create 1024 in
    let n = Array.length the_vars in
    let rec of_bdd_node i b =
      match MLBDD.inspectb b with
      | MLBDD.BIf (no, v, yes) when v = i ->
        let _ = Logs.debug (fun m -> m "Bdd->zdd: real node %d@." v) in
        mkIf (of_bdd (i + 1) no) v (of_bdd (i + 1) yes)
      | MLBDD.BFalse when i >= n - 1 -> mk Zero
      | MLBDD.BTrue when i >= n - 1 -> mk One
      | _ -> let next = of_bdd (i + 1) b in mkIf next i next
    and of_bdd i b =
      let _ = Logs.debug (fun m -> m "Bdd->zdd: %d/%d@." i n) in
      try
        H1.find visited (i, b)
      with
        | Not_found ->
          let result = of_bdd_node i b in
          let () = H1.replace visited (i, b) result in
          result
    in
    of_bdd 0 b

  let print_to_dot b ~file =
    (* Adapted from Jean-Christophe Filliâtre's bdd library*)
    let open Format in
    let module H1 = Hashtbl.Make(Core) in
    let c = open_out file in
    let fmt = formatter_of_out_channel c in
    fprintf fmt "digraph bdd {@\n";
    let visited = H1.create 1024 in
    let rec visit b =
      if not (H1.mem visited b) then
        begin
          H1.add visited b ();
          match b.node with
          | Zero ->
            fprintf fmt "%d [shape=box label=\"0\"];" b.tag
          | One ->
            fprintf fmt "%d [shape=box label=\"1\"];" b.tag
          | If{ var; no; yes; count } ->
            fprintf fmt "%d [label=\"%a (%a)\"];" b.tag V.pp var P.pp count;
            fprintf fmt "%d -> %d;@\n" b.tag yes.tag;
            fprintf fmt "%d -> %d [style=\"dashed\"];@\n" b.tag no.tag;
            visit yes;
            visit no
        end
    in
    visit b;
    fprintf fmt "}@.";
    close_out c
end
