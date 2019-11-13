
#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type tuple =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of tuple

  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr string = raise X_not_yet_implemented ;;

let read_sexprs string = raise X_not_yet_implemented;;
  
end;; (* struct Reader *)


open PC;;
open List;;
exception X_empty_list;;

(*
let parse_true = make_word char_ci "#t ";;
let parse_false = make_word char_ci "#f ";;
let parse_boolean = disj parse_true parse_false;;
(*let parse_boolean = pack parse_boolean_sensitive lowercase_ascii;;*)

(*get parsed list (first in parse_boolean result) returns bool type of sexpr 
example: 
make_boolean ['#';'T';' '];;*)
let make_boolean bool_list = 
  match bool_list with
  | [] -> raise X_empty_list
  | x::xs ->  let c = (lowercase_ascii (nth bool_list 1)) in
              (if (c = 't') then (Bool(true))
              else if (c = 'f') then (Bool(false))
              else raise X_no_match);; 
*)

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let make_spaced nt =
  make_paired (star nt_whitespace) (star nt_whitespace) nt;;

let make_boolean bool_list = 
  match bool_list with
  | [] -> raise X_empty_list
  | x::xs ->  let c = (lowercase_ascii (nth bool_list 1)) in
              (if (c = 't') then true
              else if (c = 'f') then false
              else raise X_no_match);;

(*parse_boolean (string_to_list "#T bvfhdbvdzd");;
- : bool * char list =
(true, ['b'; 'v'; 'f'; 'h'; 'd'; 'b'; 'v'; 'd'; 'z'; 'd'])
*)
let parse_boolean = 
let parse_true = make_word char_ci "#t " in
let parse_false = make_word char_ci "#f " in
let nt = disj parse_true parse_false in
let nt = pack nt make_boolean  in
nt;;


(*optional : add spaced without \n caracter around char';'*)
let parse_comment_endline = 
let nt = make_paired (char ';') (char '\n') (star(const(fun x-> Char.code x<> 10))) in
let nt = pack nt (fun x -> []) in 
nt;;

(*parse_comment_endinput (string_to_list "; jfcvnd   njvn k ndkllf     ");;
- : 'a list * char list = ([], [])
parse_comment_endinput (string_to_list "; hhhhhh 
shircb");;
Exception: PC.X_no_match. *)
let parse_comment_endinput = 
let nt = caten (char ';') (star(const(fun x-> Char.code x<> 10))) in
let nt = not_followed_by nt (char '\n') in 
let nt = pack nt (fun x -> []) in 
nt;;

let parse_line_comment = disj parse_comment_endline parse_comment_endinput;;


let parse_symbolChar = 
let nt_capital = const (fun ch -> 'A' <= ch && ch <= 'Z') in
let nt_letters = disj nt_capital (const (fun ch -> 'a' <= ch && ch <= 'z')) in 
let nt = disj nt_letters (const (fun ch -> '0' <= ch && ch <= '9')) in
let nt = disj_list ([nt; (char '!'); (char '$'); (char '^'); (char '*'); (char '-'); (char '_'); (char '='); (char '+'); (char '<'); (char '>'); (char '/'); (char '?')]) in
nt;;

(*parse_symbol (string_to_list "hbGJNJ123^!*#{ mnc mmc xk");;
- : string * char list =
("hbgjnj123^!*",
 ['#'; '{'; ' '; 'm'; 'n'; 'c'; ' '; 'm'; 'm'; 'c'; ' '; 'x'; 'k'])
 *)
let parse_symbol = 
let nt = plus parse_symbolChar  in
let nt = pack nt (fun x-> list_to_string(List.map lowercase_ascii (x))) in
nt;;


let parse_string = 
let nt_metaChar = disj_list ([(char '\r'); (char '\n'); (char '\t'); (char (Char.chr 12)); (char '\\'); (char '\"')]) in
let nt_literalChar = (const(fun x-> (Char.code x<> 34)&&(Char.code x<> 92) )) in
let nt = disj nt_literalChar nt_metaChar in
let nt = star nt in
let nt = make_paired (char '"') (char '"') nt in
make_spaced nt;;


(*parse_string (string_to_list "\"aB$ a\"shir");;
- : char list * char list =
(['"'; 'a'; 'B'; '$'; ' '; 'a'; '"'; 's'; 'h'; 'i'; 'r'], []) 

bound with '"'
parse_string (string_to_list "\"aB$ a\"shir");;
Exception: PC.X_no_match. *)

let parse_minus = char_ci '-';;
let parse_plus = char_ci '+';;
let math_sign_nt = disj (char_ci '-') (char_ci '+');;


let make_nt_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let nt = pack nt (let delta = (Char.code ch_from) - displacement in
		      fun ch -> (Char.code ch) - delta) in nt;;


(*val int : char list = ['-'; '0'; '0'; '0'; '0'; '0'; '1'; '2']
# parse_integer int;;
- : int * char list = (-12, [])
 *)
let parse_integer = 
let nt = make_nt_digit '0' '9' 0 in
let nt = plus nt in
let nt_sign = disj (char_ci '-') (char_ci '+') in
let nt_sign = maybe nt_sign in
let nt = caten nt_sign nt in
let nt = pack nt (fun tuple ->
                  match tuple
                 with
                  | (None, digits) -> List.fold_left  (fun a b -> 10 * a + b) 0 digits
                  | (Some ch, digits) ->  match ch with
                                          | '-' -> -1 * (List.fold_left (fun a b -> 10 * a + b) 0 digits)
                                          | '+' -> List.fold_left (fun a b -> 10 * a + b) 0 digits
                                          | _ -> raise X_this_should_not_happen) in
nt;;

