
let whitespace = [%sedlex.regexp? white_space]
let simple_ident = [%sedlex.regexp? Plus alphabetic]
let string_quote = [%sedlex.regexp? '"']

let rec tokenise lexbuf =
  let open Sedlexing in
  let open Parser in
  match%sedlex lexbuf with
  | whitespace -> tokenise lexbuf
  | eof -> EOF
  | 8712 | "in" -> IN
  | '=' -> EQ
  | "{" -> OPENBRACE
  | "}" -> CLOSEBRACE
  | "," -> COMMA
  | ":-" -> REVIMPL
  | "[Ranges]" | "[ranges]" -> RANGESSECTION
  | "[Rules]" | "[rules]" -> RULESSECTION
  | "[Goal]" | "[goal]" -> GOALSECTION
  | ":" -> COLON
  | "." -> PERIOD
  | "have" -> HAVEPREDICATE
  | "reach" -> REACHPREDICATE
  | simple_ident -> IDENT (Utf8.lexeme lexbuf)
  | string_quote -> make_ident lexbuf
  | _ -> failwith "Unrecognised lexical sequence"

and make_ident lexbuf =
  let acc = Buffer.create 42 in
  let rec read_string lexbuf =
    let open Sedlexing in
    [%sedlex match lexbuf with
      | string_quote -> Buffer.contents acc
      | Compl string_quote -> accumulate (Utf8.lexeme lexbuf) lexbuf
      | _ -> assert false
    ]
  and accumulate str lexbuf =
    Buffer.add_string acc str;
    read_string lexbuf
  in
  Parser.IDENT (read_string lexbuf)
