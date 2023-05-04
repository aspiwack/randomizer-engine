type 'a t =
  | One
  | Zero
  | Var of 'a
  | And of 'a t * 'a t
  | Or of 'a t * 'a t
  | Not of 'a t
  | Impl of 'a t * 'a t

let one = One
let zero = Zero
let var x = Var x
let ( && ) x y = And (x, y)
let ( || ) x y = Or (x, y)
let not x = Not x
let ( --> ) x y = Impl (x, y)
let ( <--> ) x y = (x --> y) && (y --> x)

let conj l = List.fold_left ( && ) one l
let disj l = List.fold_left ( || ) zero l
let conj_seq l = Seq.fold_left ( && ) one l
let disj_seq l = Seq.fold_left ( || ) zero l

let conj_map f l = conj (List.map f l)
let disj_map f l = disj (List.map f l)
let conj_map_seq f l = conj_seq (Seq.map f l)
let disj_map_seq f l = disj_seq (Seq.map f l)

let rec vars = function
  | One -> Seq.empty
  | Zero -> Seq.empty
  | Var x -> OSeq.return x
  | And (x, y) -> Seq.flat_map vars (List.to_seq [x; y])
  | Or (x, y) -> Seq.flat_map vars (List.to_seq [x; y])
  | Impl (x, y) -> Seq.flat_map vars (List.to_seq [x; y])
  | Not x -> vars x

let pp pp_var fmt f =
  let and_prec = 2
  and or_prec = 3
  and impl_prec = 1
  and not_prec = 4
  in
  let rec pp prec f fmt =
    match f with
    | One -> Format.fprintf fmt "1"
    | Zero -> Format.fprintf fmt "0"
    | Var x -> pp_var fmt x
    | And (x, y) when prec <= and_prec -> Format.fprintf fmt "%t && %t" (pp and_prec x) (pp and_prec y)
    | Or (x, y) when prec <= or_prec -> Format.fprintf fmt "%t || %t" (pp or_prec x) (pp or_prec y)
    | Impl (x, y) when prec <= impl_prec -> Format.fprintf fmt "%t --> %t" (pp (impl_prec + 1) x) (pp impl_prec y)
    | Not x when prec <= not_prec -> Format.fprintf fmt "~%t" (pp not_prec x)
    | f -> paren f fmt
  and paren f fmt =
    Format.fprintf fmt "(@[<hov 1>%t@])" (pp 0 f)
  in
  pp 0 f fmt
