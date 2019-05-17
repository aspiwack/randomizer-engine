exception ParseError of (Lexing.position * Lexing.position) option * String.t

type atom =
  | Have of string
  | Reach of string

type rule = atom * atom list

type range_expr =
  | RangeLiteral of string list
  | RangeIdent of string

type range =
  | RangeDecl of string * range_expr
  | RangeDef of string * range_expr

type section =
  | Rules of rule list
  | Ranges of range list
  | Goal of atom
