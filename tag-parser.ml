#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let rec tag_parse_const_helper sexp = 
match sexp with 
| Bool(_) -> sexp
| Char(_) -> sexp
| Number(_) -> sexp
| String(_) -> sexp
| TagRef(_) -> sexp
| Pair (Symbol ("quote"), cdr) -> (match cdr with 
                                              | Pair(something, Nil) -> something
                                              | _ -> cdr)
| TaggedSexpr(name, tag_value)->  let tag_value_parsed = (tag_parse_const_helper tag_value) in
                                                            TaggedSexpr(name, tag_value_parsed)
| _-> raise X_syntax_error;;

let tag_parse_const sexp = Const(Sexpr((tag_parse_const_helper sexp)));;

let tag_parse_variable sexpression = 
match sexpression with
| Symbol(name) -> if (List.mem name reserved_word_list) then raise X_syntax_error else Var(name)
| _ -> raise X_syntax_error;;

let rec get_names_from_symbol_list symbol_list =
match symbol_list with
| Pair(Symbol(first_name), rest) -> first_name :: (get_names_from_symbol_list rest)
| Symbol(name) -> [name]
| Nil -> []
| _ -> raise X_syntax_error;;

let rec is_simple_arg_list list =
  match list with
  | Pair(_, Nil) -> true
  | Symbol("vs") -> false
  | Pair(_, rest) -> is_simple_arg_list rest
  | _ -> raise X_syntax_error;;

let all_but_last list =
let rvrs = (List.rev list) in
let rvrs = (List.tl rvrs) in
(List.rev rvrs);;

let rec flatten sexpr_pairs = 
match sexpr_pairs with
| Pair(first, Nil) -> [first]
| Pair(first, rest) -> first :: (flatten rest)
| anything_else -> [anything_else];; 

let rec tag_parse_expression sexpr = 

  let tag_parse_if_expression sexpression =
    match sexpression with
    | Pair(Symbol("if"), Pair(test_sexp, Pair(dit_sexp, maybe_dif_sexp))) -> 
      let test = (tag_parse_expression test_sexp) in
      let dit = (tag_parse_expression dit_sexp) in
      let dif = (match maybe_dif_sexp with 
                  | Pair(dif_sexp, Nil) -> (tag_parse_expression dif_sexp) 
                  | Nil -> Const(Void)
                  | _ -> raise X_syntax_error) in
      If(test, dit, dif)
    | _ -> raise X_syntax_error in 

  let tag_parse_lambda_expression sexpression =
    match sexpression with
    | Pair(Symbol("lambda"), Pair(arg_list, exprs)) -> 
      let body = tag_parse_expression (Pair(Symbol("begin"), exprs)) in
      let is_simple = (is_simple_arg_list arg_list) in
      let arg_list = (get_names_from_symbol_list arg_list) in
      if (is_simple) then LambdaSimple(arg_list, body) else LambdaOpt((all_but_last arg_list), "vs", body)
    | _ -> raise X_syntax_error in

  let tag_parse_seq_expression sexpression =
    match sexpression with 
    | Pair(Symbol("begin"), sexprs) ->
      (match sexprs with
      | Pair(something, Nil) -> tag_parse_expression something
      | Pair(first, rest) -> Seq((tag_parse_expressions (flatten sexprs))) (*  which will already be seq  *)
      | Nil -> Const(Void)
      | _ -> raise X_syntax_error (**thought that through - (begin . 1) is not legal thus the sexprs cannot be not a pair nor a Nil *))
    | _ -> raise X_syntax_error in

  try (tag_parse_seq_expression sexpr)
  with X_syntax_error ->
  try (tag_parse_lambda_expression sexpr)
  with X_syntax_error ->
  try (tag_parse_if_expression sexpr)
  with X_syntax_error -> 
  try (tag_parse_const sexpr)
  with X_syntax_error ->
  try  (tag_parse_variable sexpr)
  with X_syntax_error -> raise X_not_yet_implemented
and tag_parse_expressions sexpr = 
(List.map tag_parse_expression sexpr);;

let test_string_tag scheme_code =
(tag_parse_expression (Reader.read_sexpr scheme_code));;
  
end;; (* struct Tag_Parser *)




    
