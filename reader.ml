
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
  


open PC;;
open List;;
exception X_empty_list;;
exception X_not_named_char;;


let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let make_spaced nt =
  make_paired (star nt_whitespace) (star nt_whitespace) nt;;



let parse_symbolChar = 
let nt_capital = const (fun ch -> 'A' <= ch && ch <= 'Z') in
let nt_letters = disj nt_capital (const (fun ch -> 'a' <= ch && ch <= 'z')) in 
let nt = disj nt_letters (const (fun ch -> '0' <= ch && ch <= '9')) in
let nt = disj_list ([nt; (char '!'); (char '$'); (char '^'); (char '*'); (char '-'); (char '_'); (char '='); (char '+'); (char '<'); (char '>'); (char '/'); (char '?')]) in
nt;;

(*parse_symbol (string_to_list "hbGJNJ123^!#{ mnc mmc xk");;
- : string * char list =
("hbgjnj123^!*",
 ['#'; '{'; ' '; 'm'; 'n'; 'c'; ' '; 'm'; 'm'; 'c'; ' '; 'x'; 'k'])
 *)
let parse_symbol = 
let nt = plus parse_symbolChar  in
let nt = pack nt (fun x-> Symbol(list_to_string(List.map lowercase_ascii (x)))) in
nt;;


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

let nt_float =
let base = 10 in
let nt = parse_to_number base in
let nt = caten nt (char_ci '.') in
let nt = pack nt (fun (e, _) -> e) in
let nt_right = make_nt_digit '0' '9' 0 in
let nt_right = plus nt_right in
let nt = caten nt nt_right in
let nt = pack nt (fun number ->
                  match number with
                  | (left, right) -> let sign = if (left < 0) then ( -. ) else ( +. ) in
                  let right = List.map (fun int -> float_of_int int) right in
                  (float_of_int left) +. List.fold_right (fun a b  -> (sign (b /. 10.0) (a /. 10.0))) right 0.0) in
let nt = pack nt (fun float -> Number(Float(float)))
in nt;;


let parse_float =
let base = 10 in 
let nt = parse_to_number base in
let nt = caten nt (char_ci '.') in
let nt = pack nt (fun (e, _) -> e) in
let nt_right = make_nt_digit '0' '9' 0 in
let nt_right = plus nt_right in
let nt = caten nt nt_right in
let nt = pack nt (fun number ->
                  match number with
                  | (left, right) -> let sign = if (left < 0) then ( -. ) else ( +. ) in
                                     let right = List.map (fun int -> float_of_int int) right in
                  (float_of_int left) +. List.fold_right (fun a b -> (sign (b /. 10.0) (a /. 10.0))) right 0.0) in
                  nt;;


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
                | None -> Number (Int(left_number))
                | _ -> raise X_this_should_not_happen)
                in nt;;


let nt_scientific =
let pow one mul a n =
  (let rec g p x = function
  | 0 -> x
  | i ->
      g (mul p p) (if i mod 2 = 1 then mul p x else x) (i/2)
  in
  g a one n) in
let nt_as_integer = parse_decimal in
let nt_as_integer = caten nt_as_integer (char_ci 'e') in
let nt_as_integer = caten nt_as_integer parse_decimal in
let nt_as_integer = pack nt_as_integer (fun ((coefficient, char_e), exponent) ->
                                        Number(Int(coefficient * (pow 1 ( * ) 10 exponent)))) in
let nt_as_float = parse_float in
let nt_as_float = caten nt_as_float (char_ci 'e') in
let nt_as_float = caten nt_as_float parse_decimal in
let nt_as_float = pack nt_as_float (fun ((coefficient, char_e), exponent) ->
                                    Number(Float(coefficient *. (pow 1. ( *. ) 10. exponent)))) in
let nt = disj nt_as_float nt_as_integer in 
nt;;

let nt_number = disj_list [nt_radix; nt_scientific; nt_float; nt_integer];;


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
let parse_true = make_word char_ci "#t" in
let parse_false = make_word char_ci "#f" in
let nt = disj parse_true parse_false in
let nt = not_followed_by nt parse_symbol in
let nt = pack nt make_boolean  in
nt;;

let parse_whitespaces = pack nt_whitespace (fun x-> ());;


(*parse_comment_endinput (string_to_list "; jfcvnd   njvn k ndkllf     ");;
- : 'a list * char list = ([], [])
parse_comment_endinput (string_to_list "; hhhhhh 
shircb");;
Exception: PC.X_no_match. *)

(*
parse_line_comment (string_to_list "                
;   ncxjnjckjkknck\"
         ;nxmcjdknfjdk
           ;nxmcb hjcbvhjcb:             
                    ");;
- : 'a list * char list = ([], [])
*)
(*
let parse_line_comment = 
let nt = disj parse_comment_endline parse_comment_endinput in
let nt = star nt in (* explanation: parse_line_comment (string_to_list "                
                                          ;   ncxjnjckjkknck\"
                                                  ;nxmcjdknfjdk
                  parse_to                                  ;nxmcb hjcbvhjcb:");;
                                          - : 'a list list * char list = ([[]; []; []], []) *)
let nt = pack nt (fun x-> ()) in
 nt;;
*)

let parse_comment_endline = 
let nt = make_paired (char ';') (char '\n') (star(const(fun x-> Char.code x<> 10))) in
let nt = pack nt (fun x -> ()) in 
nt;;
(*
let parse_comment_endinput = 
let nt = caten (char ';') (star(const(fun x-> Char.code x<> 10))) in
let nt = not_followed_by nt (char '\n') in  
let nt = pack nt (fun x -> ()) in 
nt;;
*)
let parse_comment_endinput =
let nt_end =  disj (pack nt_end_of_input (fun _ -> ())) (pack (char '\n') (fun _ -> ())) in
let nt = diff nt_any nt_end in
let nt = make_paired (char ';') (nt_end) (star nt) in
let nt = pack nt (fun x -> ()) in 
nt;;

let parse_line_comment = 
let nt = disj  parse_comment_endinput parse_comment_endline in
(*let nt = pack nt (fun x-> ()) in*)
 nt;;



 (*
let p  = make_nt_metaChar 'N';; val p : char list -> char * char list = <fun>
 # p (string_to_list "\\Nrest");;- : char * char list = ('\n', ['r'; 'e'; 's'; 't'])
let p  = make_nt_metaChar '\"';;  val p : char list -> char * char list = <fun>
 # p (string_to_list "\\\"rest");  - : char * char list = ('"', ['r'; 'e'; 's'; 't'])
*)
let make_nt_metaChar_letter ch = 
let nt = caten (char '\\') (char_ci ch) in
let nt = pack nt (fun (_, e) -> match (lowercase_ascii(e)) with 
                                |'r' -> (Char.chr 13)
                                |'n' -> (Char.chr 10)
                                |'t' -> (Char.chr 9)
                                |'f' -> (Char.chr 12)
                                |_ -> raise X_no_match

                  ) in
nt;;

let make_nt_metaChar_special ch = 
let nt = caten (char '\\') (char_ci ch) in
let nt = pack nt (fun (_, e) -> e) in
nt;;

(*parse_string (string_to_list "\"\\Nshir\"rest");;
- : sexpr * char list = (String "\nshir", ['r'; 'e'; 's'; 't'])
parse_string (string_to_list "\"\\\\\\\"");; ->  Exception: PC.X_no_match.*)
let parse_string = 
let nt_metaChar = disj_list ([(make_nt_metaChar_letter 'r'); (make_nt_metaChar_letter 'n'); (make_nt_metaChar_letter 't'); (make_nt_metaChar_letter 'f'); (make_nt_metaChar_special '\\'); (make_nt_metaChar_special '\"')]) in
let nt_literalChar = (const(fun x-> (Char.code x<> 34)&&(Char.code x<> 92) )) in
let nt = disj nt_literalChar nt_metaChar in
let nt = star nt in
let nt = make_paired (char '"') (char '"') nt in
let nt = pack nt (fun ch_lst -> String(list_to_string ch_lst)) in
nt;;



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

let parse_symbol_for_tag = 
let nt = plus parse_symbolChar  in
let nt = pack nt (fun x-> list_to_string(List.map lowercase_ascii (x))) in
make_spaced nt;;


(* should be without space around #{ } 
parse_tag (string_to_list "#{hi}=exp");;
- : sexpr * char list = (TagRef "hi", ['='; 'e'; 'x'; 'p'])
# parse_tag (string_to_list "    #{    vghfd$$$$123S   }    rest");;  
Exception: PC.X_no_match.
*)
let parse_tag = 
let nt_l = (word "#{") in
let nt_r =(word "}") in
let nt = make_paired  nt_l nt_r parse_symbol_for_tag in
let nt = pack nt (fun s -> s) in
nt;;



(*???? we should change the spaced into includes comments *)
let parse_parenthesized_expr nt = make_paired (make_spaced (char '(')) (make_spaced (char ')')) nt ;;



let rec check_tag_expression symbol sexp =
match sexp with
| Pair(left, right) -> (check_tag_expression symbol left) || (check_tag_expression symbol right)
| TaggedSexpr(string, sexp) -> string = symbol || (check_tag_expression symbol sexp)
| _ -> false;;

(*parse_sexpr (string_to_list "(#f)rest");;
- : sexpr * char list = (Pair (Bool false, Nil), ['r'; 'e'; 's'; 't'])

let parse_list = parse_parenthesized_expr (star (parse_sexpr)) in
let parse_list = pack parse_list (fun exp_lst-> List.fold_right (fun exp acc -> Pair(exp,acc))
                                                                exp_lst 
                                                                Nil  
                                  )in
                                  *)
let rec parse_sexpr ch_lst = (*///TODO :wrap parse list and where () and expr parser *)
let parse_sexp_comment =   (word "#;") in
let parse_sexp_comment = caten parse_sexp_comment parse_sexpr in
let parse_sexp_comment = pack parse_sexp_comment (fun x-> ()) in
let parse_comments = disj_list ([parse_whitespaces; parse_sexp_comment; parse_line_comment]) in
let parse_comments = star parse_comments in
let make_parse_comment p = make_paired (parse_comments) (parse_comments) p in

let parse_list = caten (make_parse_comment (char '(')) (star(parse_sexpr)) in
let parse_list = pack parse_list (fun (_,s)-> s) in
let parse_list = caten parse_list (make_parse_comment (char ')'))  in
let parse_list = pack parse_list (fun (s,_)-> s) in
(*let parse_list = parse_parenthesized_expr (star (parse_sexpr)) in*)
let parse_list = pack parse_list (fun exp_lst-> List.fold_right (fun exp acc -> Pair(exp,acc))
                                                                exp_lst 
                                                                Nil  
                                  )in
let parse_dottedList = caten (make_parse_comment (char '(')) (plus(parse_sexpr)) in
let parse_dottedList = pack parse_dottedList (fun (_,s)-> s) in           
let parse_dottedList = caten parse_dottedList (word ".")  in
let parse_dottedList = pack parse_dottedList (fun (s,_)-> s) in
let parse_dottedList = caten (caten parse_dottedList (parse_sexpr))  (make_parse_comment(char ')')) in
let parse_dottedList = pack parse_dottedList (fun (s,_)-> s) in
let parse_dottedList = pack parse_dottedList (fun (exp_lst, last_exp) -> List.fold_right (fun exp acc -> Pair(exp,acc))
                                                                exp_lst 
                                                                last_exp  
                                              )in

let parse_quoted = make_spaced (char (Char.chr 39))  in
let parse_quoted = caten parse_quoted parse_sexpr in
let parse_quoted = pack parse_quoted (fun (e,s)-> Pair (Symbol("quote") , Pair(s,Nil)))  in

let parse_quasiQuoted = make_spaced (char (Char.chr 96)) in
let parse_quasiQuoted = caten parse_quasiQuoted parse_sexpr in 
let parse_quasiQuoted = pack parse_quasiQuoted (fun (e,s)-> Pair (Symbol("quasiquote") , Pair(s,Nil)))  in

let parse_unquoted =  make_spaced (char (Char.chr 44)) in
let parse_unquoted = caten parse_unquoted parse_sexpr in 
let parse_unquoted = pack parse_unquoted (fun (e,s)-> Pair (Symbol("unquote") , Pair(s,Nil)))  in

let parse_unquoted_sp =  make_spaced (word ",@") in
let parse_unquoted_sp = caten parse_unquoted_sp parse_sexpr in
let parse_unquoted_sp = pack parse_unquoted_sp (fun (e,s)-> Pair (Symbol("unquote-splicing") , Pair(s,Nil))) in


let parse_taggedExp =  parse_tag in
let parse_taggedExp = caten parse_taggedExp (maybe (caten (char '=') parse_sexpr)) in   
let parse_taggedExp = pack parse_taggedExp (fun (tag, maybe_exp) -> 
                  match maybe_exp with
                  | None -> TagRef(tag)
                  | Some(eq, sexp) -> if (check_tag_expression tag sexp) then TaggedSexpr(tag, sexp) else raise X_this_should_not_happen)
in

let nt = disj_list ([parse_boolean ; parse_char ; nt_number ;parse_string ; parse_symbol ; parse_quoted ; parse_quasiQuoted; parse_unquoted; parse_unquoted_sp; parse_list; parse_dottedList; parse_taggedExp]) in
make_parse_comment nt ch_lst;;



(*EXAMPLES:
utop # parse_sexpr (string_to_list "  ' 5a  rest");;
- : sexpr * char list =
(Pair (Symbol "quote", Pair (Symbol "5a", Nil)), ['r'; 'e'; 's'; 't'])
─( 12:36:26 )─< command 1 >────────────────────────────────────────────────────────{ counter: 0 }─
utop # parse_sexpr (string_to_list "  ,@  #f  rest");;
- : sexpr * char list =
(Pair (Symbol "unquote-splicing", Pair (Bool false, Nil)),
 ['r'; 'e'; 's'; 't'])
 *)

  let extract_AST(ast,rest) = ast;;

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

let read_sexpr string = extract_AST (parse_sexpr (string_to_list string)) ;;
(*raise X_not_yet_implemented ;;*)

let read_sexprs string = extract_AST ((star parse_sexpr) (string_to_list string)) ;;(*raise X_not_yet_implemented;;*)
  
end;; (* struct Reader *)
