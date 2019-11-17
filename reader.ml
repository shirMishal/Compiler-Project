
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
exception X_not_named_char;;

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

let make_nt_parenthesized_expr nt =
  let nt1 = make_paired (make_spaced (char '(')) 
			(make_spaced (char ')')) nt in
  let nt2 = make_paired (make_spaced (char '[')) 
			(make_spaced (char ']')) nt in
  let nt3 = make_paired (make_spaced (char '{'))
			(make_spaced (char '}')) nt in
  let nt = disj nt1 (disj nt2 nt3) in
  nt;;


let make_boolean bool_list = 
  match bool_list with
  | [] -> raise X_empty_list
  | x::xs ->  let c = (lowercase_ascii (nth bool_list 1)) in
              (if (c = 't') then Bool(true)
              else if (c = 'f') then Bool(false)
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
let nt = plus nt in
let nt = make_spaced nt in
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
(*
parse_line_comment (string_to_list "                
;   ncxjnjckjkknck\"
         ;nxmcjdknfjdk
           ;nxmcb hjcbvhjcb:             
                    ");;
- : 'a list * char list = ([], [])
*)
let parse_line_comment = 
let nt = disj parse_comment_endline parse_comment_endinput in
let nt = star nt in (* explanation: parse_line_comment (string_to_list "                
                                          ;   ncxjnjckjkknck\"
                                                  ;nxmcjdknfjdk
                                                    ;nxmcb hjcbvhjcb:");;
                                          - : 'a list list * char list = ([[]; []; []], []) *)
let nt = pack nt List.flatten in
make_spaced nt;;

let parse_sexpCommentPrefix = make_spaced(word "#;");;
(*let parse_sexp =  complete


let parse_sexp_comment =
let nt = caten parse_sexpCommentPrefix parse_sexp in
let nt = pack nt (fun (_,_)-> nul) in
make_spaced nt;;
*)


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
let nt = pack nt (fun x-> Symbol(list_to_string(List.map lowercase_ascii (x)))) in
nt;;

(*
let parse_string = 
let nt_metaChar = disj_list ([(char '\r'); (char '\n'); (char '\t'); (char (Char.chr 12)); (char '\\'); (char '\"')]) in
let nt_literalChar = (const(fun x-> (Char.code x<> 34)&&(Char.code x<> 92) )) in
let nt = disj nt_literalChar nt_metaChar in
let nt = star nt in
let nt = make_paired (char '"') (char '"') nt in
make_spaced nt;;

let convert_metachar = (fun lst-> (char (nth lst 1 )));;
let nt_metaChar = 
let nt = disj_list ([(char '\r'); (char '\n'); (char '\t'); (char (Char.chr 12)); (char '\\'); (char '\"')]) in
let nt = make_paired (char '\"') (char '\"') nt in
nt;;

let nt = disj_list ([caten (char '\\')(char '\r'); caten (char '\\')(char '\n'); caten (char '\\')(char '\t'); caten (char '\\')(char (Char.chr 12)); caten (char '\\')(char '\\'); caten (char '\\')(char '\"')]) in*)
 
let nt_metaChar = 
let nt = disj_list ([(char_ci '\r'); (char_ci '\n'); (char_ci '\t'); (char_ci (Char.chr 12)); (char '\\'); (char '\"')]) in
let nt = make_paired (char '\"') (char '\"') nt in
nt;;

let parse_string = 
let nt_metaChar = disj_list ([(char '\r'); (char '\n'); (char '\t'); (char (Char.chr 12)); (char '\\'); (char '\"')]) in
let nt_literalChar = (const(fun x-> (Char.code x<> 34)&&(Char.code x<> 92) )) in
let nt = disj nt_literalChar nt_metaChar in
(*let nt = star nt in*)
let nt = make_paired (char '\"') (char '\"') nt in
nt;;

(*parse_string (string_to_list "\"aB$ a\"shir");;
- : char list * char list =
(['"'; 'a'; 'B'; '$'; ' '; 'a'; '"'; 's'; 'h'; 'i'; 'r'], []) 

bound with '"'
parse_string (string_to_list "\"aB$ a\"shir");;
Exception: PC.X_no_match. *)

let parse_namedChar = 
let nt = disj_list ([(word_ci "newline"); (word_ci "nul");(word_ci "page");(word_ci "return");(word_ci "space");(word_ci "tab");]) in 
let nt = pack nt (fun word_lst-> match (list_to_string(List.map lowercase_ascii (word_lst) ) )
                                with
                                |"newline" -> (Char.chr 10)
                                |"nul" -> (Char.chr 0)
                                |"page" -> (Char.chr 12)
                                |"return" -> (Char.chr 13)
                                |"space" -> (Char.chr 32)
                                |"tab" -> (Char.chr 9)
                                |_ -> raise X_not_named_char (*???? not sure we need it ... maybe for warnings *)
                  ) in
nt;;
let parse_visibleSimple = const (fun ch -> ch > ' ');;
let parse_charPrefix = word "#\\";;

(* parse_char (string_to_list "#\\a  ");;- : char * char list = ('a', [' '; ' '])
parse_char (string_to_list "#\\tab \\");;- : char * char list = ('\t', [' '; '\\'])
parse_char (string_to_list "#\\ abc");;Exception: PC.X_no_match.
include spaced results:
parse_char (string_to_list "    #\\nul   abc");;- : char * char list = ('\000', ['a'; 'b'; 'c'])
??? we should think if spaced needed after char*)
let parse_char =
let nt = disj parse_namedChar parse_visibleSimple in
let nt = caten parse_charPrefix nt in
let nt = pack nt (fun (_,ch)-> Char (ch)) in
make_spaced nt;;

(* parse nil input (;njxsk 
        #;a      );hi)
        shoud return (nil,[])
*)
let parse_minus = char_ci '-';;
let parse_plus = char_ci '+';;
let math_sign_nt = disj (char_ci '-') (char_ci '+');;


let make_nt_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let nt = pack nt (let delta = (Char.code ch_from) - displacement in
		      fun ch -> (Char.code ch) - delta) in nt;;

let nt_all_digits = 
let nt = make_nt_digit '0' '9' 0 in
let nt = disj nt (make_nt_digit 'a' 'z' 10) in
let nt = disj nt (make_nt_digit 'A' 'Z' 10) in
nt;;


(* help function - not for outter usage*)
let parse_to_number base = 
let nt = nt_all_digits in
let nt = plus nt in
let nt_sign = disj (char_ci '-') (char_ci '+') in
let nt_sign = maybe nt_sign in
let nt = caten nt_sign nt in
let nt = pack nt (fun tuple ->
                  (match tuple with
                  | (None, digits) -> List.fold_left  (fun a b -> base * a + b) 0 digits
                  | (Some ch, digits) ->  match ch with
                                          | '-' -> (-1) * (List.fold_left (fun a b -> base * a + b) 0 digits)
                                          | '+' -> List.fold_left (fun a b -> base * a + b) 0 digits
                                          |  _ -> raise X_this_should_not_happen)) in nt;;

let parse_decimal = 
let base = 10 in
let nt = make_nt_digit '0' '9' 0 in
let nt = plus nt in
let nt_sign = disj (char_ci '-') (char_ci '+') in
let nt_sign = maybe nt_sign in
let nt = caten nt_sign nt in
let nt = pack nt (fun tuple ->
                  (match tuple with
                  | (None, digits) -> List.fold_left  (fun a b -> base * a + b) 0 digits
                  | (Some ch, digits) ->  match ch with
                                          | '-' -> (-1) * (List.fold_left (fun a b -> base * a + b) 0 digits)
                                          | '+' -> List.fold_left (fun a b -> base * a + b) 0 digits
                                          |  _ -> raise X_this_should_not_happen)) in nt;;

let make_nt_number base =
if (base > 36) 
then raise X_no_match
else let nt = parse_to_number base in
let nt = pack nt (fun number ->
                  Number(Int(number))) in
nt;;

let parse_to_float base =
let nt = parse_to_number base in
let nt = caten nt (char_ci '.') in
let nt = pack nt (fun (e, _) -> e) in
let nt_right = make_nt_digit '0' '9' 0 in
let nt_right = plus nt_right in
let nt = caten nt nt_right in
let nt = pack nt (fun number ->
                  match number with
                  | (left, right) -> let right = List.map (fun int -> float_of_int int) right in
                  (float_of_int left) +. List.fold_right (fun a b -> (b /. 10.0 +. a /. 10.0)) right 0.0) in

nt



(*val int : char list = ['-'; '0'; '0'; '0'; '0'; '0'; '1'; '2']
# parse_integer int;;
- : int * char list = (-12, [])
 *)
let nt_integer = make_nt_number 10;;


let nt_radix = 
let nt = (caten parse_decimal (char_ci 'r')) in
let nt = caten nt (plus nt_all_digits) in
let nt = caten nt (maybe (caten (char_ci '.') (plus nt_all_digits))) in
let nt = pack nt (fun (((base, char_r), left_of_dot), x) -> 
                let left_number = List.fold_left (fun a b -> base * a + b) 0 left_of_dot in
                match x with
                | Some ('.', right_of_dot) ->  let right_dot_as_float = List.map float_of_int right_of_dot  in
                          let base_float = float_of_int base in
                          let left_number_float = (float_of_int left_number) in
                          Number (Float (left_number_float +. (List.fold_right (fun a b -> a /. base_float +. b /. base_float) right_dot_as_float 0.0)))
                | None -> Number (Int(left_number)))
                in nt;;