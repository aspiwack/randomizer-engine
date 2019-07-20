module Variable = struct

  include CCString

  let pp fmt s = Format.fprintf fmt "%s" s

  module Set = Set.Make(CCString)
  module Map = Map.Make(CCString)
end

module Location = Variable

module Item = Variable

module IndexedItem = struct

  (* Stands for a specific copy of an item which may have several copies. *)

  type t = Item.t * int

  let compare = CCPair.compare Item.compare CCInt.compare
  let equal = CCPair.equal Item.equal CCInt.equal

  let hash (item,k) = CCHash.(combine2 (Item.hash item) (int k))

  let pp fmt (item,k) = Format.fprintf fmt "%a_%i" Item.pp item k
end

module RangeConstraint = struct
  type t = {
    scrutinee: Item.t;
    range: Location.t list;
  }

  let pp fmt {scrutinee;range} =
  Format.fprintf fmt "%s ∈ {%a}" scrutinee (CCList.pp CCString.pp) range

end

module Atom = struct

  type 'i t =
    | Reach of Location.t
    | Have of 'i * int
    | Assign of Location.t * 'i
    (* Assign doesn't come from parsing: it appears in translations.*)

  let compare item_compare al ar = match al, ar with
    | Assign(locl,iteml), Assign(locr, itemr) ->
      CCPair.compare Location.compare item_compare (locl,iteml) (locr,itemr)
    | Assign _, _ -> -1
    | _, Assign _ -> 1
    | Reach locl, Reach locr ->
      Location.compare locl locr
    | Reach _, _ -> -1
    | _, Reach _ -> 1
    | Have(iteml, kl), Have(itemr, kr) ->
      CCPair.compare item_compare CCInt.compare (iteml, kl) (itemr, kr)
  let equal item_equal al ar = match al, ar with
    | Assign(locl,iteml), Assign(locr, itemr) ->
      Location.equal locl locr && item_equal iteml itemr
    | Reach locl, Reach locr ->
      Location.equal locl locr
    | Have(iteml,kl), Have(itemr,kr) ->
      item_equal iteml itemr && CCInt.equal kl kr
    | _ -> false

  let hash hash_item = function
    | Reach l -> CCHash.(combine2 (int 0) (Location.hash l))
    | Have (i, n) -> CCHash.(combine3 (int 1) (hash_item i) (int n))
    | Assign (l,i) -> CCHash.(combine3 (int 2) (Location.hash l) (hash_item i))

  let map f = function
    | Reach l -> Reach l
    | Have (i, n) -> Have (f i, n)
    | Assign (l, i) -> Assign (l, f i)

  let pp pp_item fmt = function
    | Reach l -> Format.fprintf fmt "reach: %a" Location.pp l
    | Have (i,1) -> Format.fprintf fmt "have: %a" pp_item i
    | Have (i,n) -> Format.fprintf fmt "have: %a * %i" pp_item i n
    | Assign(l,i) -> Format.fprintf fmt "%a ∈ %a" pp_item i Location.pp l

end

module Clause = struct

  type t = {
    goal: Item.t Atom.t;
    requires: Item.t Atom.t list
  }

end

module StringMap = Map.Make(CCString)

type program = {
  locations: Location.t list;
  (* Future plan for item: there can be more than one of an item in
     the pool. In which case it will be translated to n variables
     (where n is the number of occurrences of that item in the pool),
     the corresponding range_constraints will be translated to
     formulas which ensure that the n variables are ordered (to avoid
     generating many semantically equal shuffles) *)
  pool: Item.t list;
  range_constraints: RangeConstraint.t list;
  range_definitions: Location.t list StringMap.t;
  logic: Clause.t list;
  goal: Item.t Atom.t
}
let pp_timed_atom pp_item fmt = let open Provable in function
  | Selection a -> Atom.pp pp_item fmt a
  | At(a,i) -> Format.fprintf fmt "%a @ %i" (Atom.pp pp_item) a i
  | Action (n, i) -> Format.fprintf fmt "%s @ %i" n i

let pp_clause fmt {Clause.goal;requires} =
  Format.fprintf fmt "%a :- @[<hov>%a@]" (Atom.pp Item.pp) goal (CCList.pp ~sep:"," (Atom.pp Item.pp)) requires
let pp_program fmt prog =
  (* XXX: I'm not printing range_definitions *)
  let pp_locations = CCList.pp (fun fmt l -> Format.fprintf fmt "@[<h>%s@]" l) in
  let pp_pool = CCList.pp (fun fmt i -> Format.fprintf fmt "@[<h>%s@]" i) in
  let pp_ranges = CCList.pp RangeConstraint.pp in
  let pp_logic = CCList.pp pp_clause in
  let pp_goal fmt g = Format.fprintf fmt "%a." (Atom.pp Item.pp) g in
  Format.fprintf fmt "@[<v>@[<v 2>[Locations]@,%a@]@,@[<v 2>[Pool]@,%a@]@,@[<v 2>[Ranges]@,%a@]@,@[<v 2>[Logic]@,%a@]@,@[<v 2>[Goal]@,%a@]@]@." pp_locations prog.locations pp_pool prog.pool pp_ranges prog.range_constraints pp_logic prog.logic pp_goal prog.goal

module AtomSet = Set.Make (struct type t = Item.t Atom.t let compare = Atom.compare Item.compare end)
module AtomMap = Map.Make (struct type t = Item.t Atom.t let compare = Atom.compare Item.compare end)
module TimedAtomSet = Set.Make (struct type t = Item.t Atom.t Provable.timed let compare = compare end)
module TimedAtomMap = Map.Make (struct type t = Item.t Atom.t Provable.timed let compare = compare end)
