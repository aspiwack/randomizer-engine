module type Type = sig

  (* Type with the basic functions used pervasively throughout the randomizer engine.*)

  type t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int

  val pp : Format.formatter -> t -> unit
end

module Empty = struct

  type t = { ef: 'a. 'a }

  let absurd v = v.ef

  let empty v _w = v.ef
  let compare v _w = v.ef
  let hash v = v.ef

  let pp _fmt v = v.ef
end

module Either (L: Type) (R: Type) = struct

  type t =
    | Left of L.t
    | Right of R.t

  let equal x y =
    match x, y with
    | Left x, Left y -> L.equal x y
    | Right x, Right y -> R.equal x y
    | _ -> false

  let compare x y =
    match x, y with
    | Left x, Left y -> L.compare x y
    | Left _, _ -> -1
    | _, Left _ -> 1
    | Right x, Right y -> R.compare x y

  let hash = function
    | Left x -> CCHash.(combine2 (int 0) (L.hash x))
    | Right x -> CCHash.(combine2 (int 1) (R.hash x))

  let pp fmt = function
    | Left x -> L.pp fmt x
    | Right x -> R.pp fmt x
end

module Variable = struct

  include CCString

  let pp fmt s = Format.fprintf fmt "%s" s

  module Set = Set.Make(CCString)
  module Map = Map.Make(CCString)
end

module Location = Variable

module Item = Variable

module IndexedItem = struct

  (* Stands for a number of copies of an item which may have several copies. *)

  type t = { item: Item.t; index: int }

  let make item index = { item; index }

  let compare { item = iteml; index = indexl } { item = itemr; index = indexr } =
    CCOrd.(Item.compare iteml itemr <?> (CCInt.compare, indexl, indexr))
  let equal { item = iteml; index = indexl } { item = itemr; index = indexr } =
    Item.equal iteml itemr && CCInt.equal indexl indexr

  let hash { item; index } = CCHash.(combine2 (Item.hash item) (int index))

  let pp fmt { item; index } = Format.fprintf fmt "%a_%i" Item.pp item index
end

module MultipliedItem = struct

  (* Stands for a specific copy of an item which may have several copies. *)

  type t = Item.t * int

  let compare = CCPair.compare Item.compare CCInt.compare
  let equal = CCPair.equal Item.equal CCInt.equal

  let hash (item, k) = CCHash.(combine2 (Item.hash item) (int k))

  let pp fmt = function
    | (item, 1) -> Format.fprintf fmt "%a" Item.pp item
    | (item, k) -> Format.fprintf fmt "%a * %i" Item.pp item k
end

module RangeConstraint = struct
  type t = {
    scrutinee: Item.t;
    range: Location.t list;
  }

  let pp fmt { scrutinee; range } =
    Format.fprintf fmt "%s ∈ {%a}" scrutinee (CCList.pp CCString.pp) range
end

module Atom = struct

  type ('p, 'i) t =
    | Reach of Location.t
    | Have of 'p (* XXX: The goal is to separate the `'i` in Have and the `'i` in Assign so that `Have` can be an item w/ multiplicity (we can drop the `int` from the constructor that way, and it will be better when we decompose in the multiplicity transformation, it will make more sense) and `Assign` can mention individualised items, because it's the only thing that would make sense. All that going into the provable transformation, which needs to be performed before the multiplicity transformation as it requires implicational clauses (including clauses involving assignment!).*)
    | Assign of Location.t * 'i
  (* Assign doesn't come from parsing: it appears in translations.*)

  let compare possession_compare item_compare al ar =
    match al, ar with
    | Assign (locl, iteml), Assign (locr, itemr) ->
      CCPair.compare Location.compare item_compare (locl, iteml) (locr, itemr)
    | Assign _, _ -> -1
    | _, Assign _ -> 1
    | Reach locl, Reach locr ->
      Location.compare locl locr
    | Reach _, _ -> -1
    | _, Reach _ -> 1
    | Have iteml, Have itemr ->
      possession_compare iteml itemr
  let equal possession_equal item_equal al ar =
    match al, ar with
    | Assign (locl, iteml), Assign (locr, itemr) ->
      Location.equal locl locr && item_equal iteml itemr
    | Reach locl, Reach locr ->
      Location.equal locl locr
    | Have iteml, Have itemr ->
      possession_equal iteml itemr
    | _ -> false

  let hash hash_possession hash_item = function
    | Reach l -> CCHash.(combine2 (int 0) (Location.hash l))
    | Have i -> CCHash.(combine2 (int 1) (hash_possession i))
    | Assign (l, i) -> CCHash.(combine3 (int 2) (Location.hash l) (hash_item i))

  let map f_possession f_item = function
    | Reach l -> Reach l
    | Have i -> Have (f_possession i)
    | Assign (l, i) -> Assign (l, f_item i)

  let pp pp_possession pp_item fmt = function
    | Reach l -> Format.fprintf fmt "reach: %a" Location.pp l
    | Have i -> Format.fprintf fmt "have: %a" pp_possession i
    | Assign (l, i) -> Format.fprintf fmt "%a ∈ %a" pp_item i Location.pp l

  module Make (P: Type) (I: Type) = struct

    module Core = struct
      type nonrec t = (P.t, I.t) t

      let equal = equal P.equal I.equal
      let compare = compare P.compare I.compare
      let hash = hash P.hash I.hash

      let pp = pp P.pp I.pp
    end

    include Core

    module Set = Set.Make(Core)
    module Map = Map.Make(Core)
  end
end

module Clause = struct

  type t = {
    goal: (MultipliedItem.t, Empty.t) Atom.t;
    requires: (MultipliedItem.t, Empty.t) Atom.t list
  }
end

module StringMap = Map.Make(CCString)

(* XXX: everything below this deserves to be reorganised. *)

type program = {
  locations: Location.t list;
  pool: (Item.t * int) list;
  range_constraints: RangeConstraint.t list;
  range_definitions: Location.t list StringMap.t;
  logic: Clause.t list;
  goal: (MultipliedItem.t, Empty.t) Atom.t
}

let pp_clause fmt { Clause.goal; requires } =
  Format.fprintf
    fmt
    "%a :- @[<hov>%a@]"
    (Atom.pp MultipliedItem.pp Empty.pp)
    goal
    (CCList.pp ~pp_sep: CCFormat.(const string ",") (Atom.pp MultipliedItem.pp Empty.pp))
    requires
let pp_program fmt prog =
  (* XXX: I'm not printing range_definitions *)
  let pp_locations = CCList.pp (fun fmt l -> Format.fprintf fmt "@[<h>%s@]" l) in
  let pp_pool = CCList.pp (fun fmt (i, n) -> Format.fprintf fmt "@[<h>%s*%i@]" i n) in
  let pp_ranges = CCList.pp RangeConstraint.pp in
  let pp_logic = CCList.pp pp_clause in
  let pp_goal fmt g = Format.fprintf fmt "%a." (Atom.pp MultipliedItem.pp Empty.pp) g in
  Format.fprintf fmt "@[<v>@[<v 2>[Locations]@,%a@]@,@[<v 2>[Pool]@,%a@]@,@[<v 2>[Ranges]@,%a@]@,@[<v 2>[Logic]@,%a@]@,@[<v 2>[Goal]@,%a@]@]@." pp_locations prog.locations pp_pool prog.pool pp_ranges prog.range_constraints pp_logic prog.logic pp_goal prog.goal

module ItemAtom = Atom.Make(Item)(Item)
module AtomSet = ItemAtom.Set
module AtomMap = ItemAtom.Map
