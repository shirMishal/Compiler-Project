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
	
                       
exception X_syntax_error of string;;
exception X_lambda_error of sexpr;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list

  (* to delete *)
  val cond_expantion : sexpr -> sexpr
  val flatten : sexpr -> sexpr list
  val handle_empty : sexpr -> sexpr
  val make_param_list : sexpr list -> sexpr list
  val make_val_list : sexpr list -> sexpr list
  
  val make_sexp_vals : sexpr list -> sexpr 
  val make_sexp_params : sexpr list -> sexpr
  val let_expantion : sexpr -> sexpr -> sexpr
  (*to here*)
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

(* Help functions *)

(*raise X_error ("cond")*)
exception X_this_shouldnt_happen_error of string;;

let rec get_names_from_symbol_list symbol_list =
match symbol_list with
| Pair(Symbol(first_name), rest) -> first_name :: (get_names_from_symbol_list rest)
| Symbol(name) -> [name]
| Nil -> []
| _ -> raise (X_syntax_error "get_names_from_symbol_list");;

let rec is_simple_arg_list list =
  match list with
  | Pair(_, Nil) -> true
  | Symbol(_) -> false
  | Pair(_, rest) -> is_simple_arg_list rest
  | _ -> raise (X_syntax_error "is_simple_arg_list");;

let last_to_front list =
let rvrs = (List.rev list) in
let head = (List.hd rvrs) in
let rvrs = (List.tl rvrs) in
head::(List.rev rvrs);;

let rec flatten sexpr_pairs = 
match sexpr_pairs with
| Pair(first, Nil) -> [first]
| Pair(first, rest) -> first :: (flatten rest)
| anything_else -> [anything_else];; 



let rec quasiquote_expantion quasiqouted_sexp =
match quasiqouted_sexp with
| Pair(Symbol("unquote"), Pair(sexp, Nil)) -> sexp
| Pair(Pair(Symbol("unquote-splicing"), Pair(car, Nil)), cdr) -> Pair(Symbol("append"), Pair(car, Pair((quasiquote_expantion cdr), Nil)))
| Pair(car, Pair(Symbol "unquote-splicing", Pair(spliced_sexp, Nil))) -> Pair(Symbol("cons"), Pair((quasiquote_expantion car), Pair(spliced_sexp, Nil)))
| Pair(Symbol("unquote-splicing"), sexp) -> raise (X_syntax_error "from qq-splicing")
| Pair(car, cdr) -> Pair(Symbol("cons"), Pair((quasiquote_expantion car), Pair((quasiquote_expantion cdr), Nil)))
| Nil -> Pair(Symbol("quote"), Pair(Nil, Nil))
| Symbol(name) -> Pair(Symbol("quote"), Pair(Symbol(name), Nil))
| _ -> quasiqouted_sexp;;


let rec cond_expantion cond_ribs_sexp = 
match cond_ribs_sexp with                        
| Pair(Pair (test, Pair(Symbol("=>"), Pair(proc, Nil))), rest_ribs) -> 
  (match rest_ribs with
  | Nil -> Pair (Symbol "let",                                                                                                                                       
 Pair                                                                                                                                                     
  (Pair (Pair (Symbol "value", Pair (test, Nil)),
    Pair
     (Pair (Symbol "f",
       Pair (Pair (Symbol "lambda", Pair (Nil, Pair (proc, Nil))),
        Nil)),
      Nil)),
  Pair
   (Pair (Symbol "if",
     Pair (Symbol "value",
      Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Nil))),
   Nil)))
  | _ -> Pair (Symbol "let",                                                                                                                                       
      Pair                                                                                                                                                     
        (Pair (Pair (Symbol "value", Pair (test, Nil)),
          Pair
          (Pair (Symbol "f",
            Pair (Pair (Symbol "lambda", Pair (Nil, Pair (proc, Nil))),
              Nil)),
          Pair
            (Pair (Symbol "rest",
              Pair
              (Pair (Symbol "lambda", Pair (Nil, Pair ((cond_expantion rest_ribs), Nil))),
              Nil)),
            Nil))),
        Pair
        (Pair (Symbol "if",
          Pair (Symbol "value",
            Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
            Pair (Pair (Symbol "rest", Nil), Nil)))),
        Nil))))
| Pair (Pair (Symbol "else", then_do), rest_ribs) -> Pair(Symbol "begin", then_do)
(*Pair(Symbol "if", Pair( Bool true,  Pair(Pair(Symbol"begin" , then_do), Nil)))*)                                                                                                
| Pair(Pair(test1, then_sexp), rest_ribs)-> Pair(Symbol "if", Pair(test1, Pair(Pair(Symbol "begin", then_sexp), (match rest_ribs with
                                                                                                                                                |Nil -> Nil
                                                                                                                           |_-> Pair((cond_expantion rest_ribs), Nil)))))        
|_ -> cond_ribs_sexp;;

let rec and_expantion args =
match args with
| Nil -> Bool (true)
| Pair(one_arg , Nil) -> one_arg
| Pair(first_arg, rest_args) -> Pair(Symbol "if", Pair(first_arg, Pair((and_expantion rest_args), Pair(Bool false, Nil))))
| _ -> raise(X_syntax_error "and_expantion") 
;;
(*
Pair(Symbol "a", Pair(Symbol "s", Pair(Symbol "b", Pair(Symbol "d", Pair(Symbol "s", Nil)))))

test_ "(and a s b d s)" (If (Var "a",
              If (Var "s",
                If (Var "b", If (Var "d", Var "s", Const (Sexpr (Bool false))),
                Const (Sexpr (Bool false))),
                Const (Sexpr (Bool false))),
              Const (Sexpr (Bool false))));;
*)
let handle_empty sexp =
(*if parm lst is empty vals_sexp equals to Pair(Nil, Nil) -should handle *)
match sexp with 
|Pair (Nil, Nil) -> Nil
|_ -> sexp;;

let make_param_list binding_lst = List.map (fun sexp -> (match sexp with |Nil-> Nil 
                                                         |Pair(name , value) -> name
                                                         |_-> raise (X_syntax_error "let_expantion params_list"))
                            ) binding_lst;;
let make_val_list binding_lst = List.map (fun sexp -> (match sexp with |Nil-> Nil 
                                                      |Pair(name , Pair (value, Nil)) -> value
                                                      |_-> raise (X_syntax_error "let_expantion val_list"))
                            ) binding_lst;;
let make_sexp_params params_list = handle_empty (List.fold_right (fun exp acc -> Pair(exp,acc))
                                                                params_list 
                                                                Nil );;
let make_sexp_vals val_list = handle_empty  (List.fold_right (fun exp acc -> Pair(exp,acc))
                                                                val_list 
                                                                Nil );;                                                   
let rec let_expantion pram_lst  body =
let binding_lst = flatten pram_lst in
let params_list = (make_param_list binding_lst) in
let val_list =  (make_val_list binding_lst) in
let params_sexp = (make_sexp_params params_list)     in
let vals_sexp = (make_sexp_vals val_list)   in
Pair(
  Pair(Symbol "lambda", Pair(params_sexp, body)),
  vals_sexp)
;;
(*
Pair(Pair(Symbol "lambda", Pair(Nil, Pair(Number (Int 3), Nil))), Nil)
Pair(Symbol "let", Pair(
                      Pair(Pair(Symbol "x1", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "x2", Pair(Number (Int 2), Nil)), Nil)), 
                        Pair(Pair(Symbol "+", Pair(Symbol "x1", Pair(Symbol "x2", Nil))), Nil)))
Pair(
  Pair(Symbol "lambda", Pair(Pair(Symbol "x1", Pair(Symbol "x2", Nil)), Pair(Pair(Symbol "+", Pair(Symbol "x1", Pair(Symbol "x2", Nil))), Nil))),
   Pair(Number (Int 1), Pair(Number (Int 2), Nil)))
*)
(*
> (print-template '((a 1)))
Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Nil)
> (print-template '((a 1) (b 2)))
Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "b", Pair(Number (Int 2), Nil)), Nil))
*)

let rec letStar_expantion pram_lst  body = 
match pram_lst with
| Nil -> Pair (Symbol "let", Pair(pram_lst , body))
| Pair(rib1, Nil) -> Pair (Symbol "let", Pair(pram_lst , body))
(*ribs contains more then one element *)
| Pair (rib1, rest_ribs) -> Pair (Symbol "let", Pair( Pair (rib1,Nil) ,Pair ((letStar_expantion rest_ribs body),Nil)))
|_ -> raise (X_syntax_error "from letStar")
;;
(*
(print-template '(let* ((x 1) (y (+ x 1))) (+ x y) ))
 parm list - :  Pair(Pair(Pair(Symbol "x", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "y", Pair(Pair(Symbol "+", Pair(Symbol "x", Pair(Number (Int 1), Nil))), Nil)), Nil)), 
 body-:         Pair(Pair(Symbol "+", Pair(Symbol "x", Pair(Symbol "y", Nil))), Nil)  )
*)

(*let new_vals_list = List.map (fun rib_sexp -> (match rib_sexp with  
                                                      |Pair(name , Pair (value, Nil)) -> value 
                                                      |_-> raise (X_syntax_error "letrec_expantion val_list"))
                            ) binding_lst in*)
let quoted_whatever = Pair(Symbol "quote", Pair(Symbol "whatever", Nil));;
let create_nested_pairs sexp_list =  List.fold_right (fun exp acc -> Pair(exp,acc))
                                                                sexp_list 
                                                                Nil ;;
let create_nested_pairs_improper sexp_list x = List.fold_right (fun exp acc -> Pair(exp,acc))
                                                                sexp_list 
                                                                x ;;


let  letRec_expantion param_list body = 
match param_list with
| Nil -> Pair (Symbol "let", Pair(param_list , body))
| Pair (rib1, rest_ribs) -> (
  let binding_lst = flatten param_list in
  let new_param_list = List.map (fun rib_sexp -> (match rib_sexp with  
                                                      |Pair(name , Pair (value, Nil)) -> Pair(name , Pair (quoted_whatever, Nil))
                                                      |_-> raise X_this_should_not_happen)
                            ) binding_lst in
  let new_param_pairs = (create_nested_pairs new_param_list)in 
  let set_list = List.map (fun single_rib -> Pair(Symbol "set!", single_rib)) binding_lst in
  let new_body = (match body with |Pair(Pair(op, args), Nil) -> Pair(op, args)
                                  |Nil -> raise( X_syntax_error "") 
                                  |_ -> body ) in
  (*let new_body = Pair(Symbol "let", Pair(Nil, body)) in*)
  let nested_pairs_set_body = (create_nested_pairs (List.append set_list [new_body])) in
  Pair(Symbol "let", Pair(new_param_pairs, nested_pairs_set_body))
)
| _ -> raise X_this_should_not_happen;;
(*
> (print-template '(let (ribs_list) (set!1) (set!2) body))
Pair(Symbol "let", Pair(Pair(Symbol "ribs_list", Nil), Pair(Pair(Symbol "set!1", Nil), Pair(Pair(Symbol "set!2", Nil), Pair(Symbol "body", Nil)))))
*)

(*
Pair(Symbol "letrec", Pair(
  bindings: -  Pair(Pair(Symbol "fact", Pair(Pair(Symbol "lambda", Pair(Pair(Symbol "n", Nil), Pair(Pair(Symbol "if", Pair(Pair(Symbol "=", Pair(Symbol "n", Pair(Number (Int 0), Nil))), Pair(Number (Int 1), Pair(Pair(Symbol "*", Pair(Symbol "n", Pair(Pair(Symbol "fact", Pair(Pair(Symbol "-", Pair(Symbol "n", Pair(Number (Int 1), Nil))), Nil)), Nil))), Nil)))), Nil))), Nil)), Nil)   ,  
  body                 Pair(Pair(Symbol "fact", Pair(Number (Int 3), Nil)), Nil)                     ))
*)
let rec tag_parse_expression sexpr = 
  (* Macro expantions *)

  match sexpr with
  (* qq-expantion *)
  | Pair(Symbol("quasiquote"), Pair(quasiquoted_sexp, Nil)) -> (tag_parse_expression (quasiquote_expantion quasiquoted_sexp))
  
  (* cond-expantion *)
  | Pair (Symbol "cond", cond_ribs_sexp)-> (match cond_ribs_sexp with
                                            | Nil -> raise (X_syntax_error "from cond expantion")
                                            | _ -> (tag_parse_expression (cond_expantion cond_ribs_sexp)))
  (* and-expantion *)
  | Pair (Symbol "and", args) -> (tag_parse_expression (and_expantion args))
 
  (* let-expantion Pair(Symbol "let", Pair(Nil, Pair(Number (Int 3), Nil)))
                     result: Pair (Pair (Symbol "lambda", Pair (Nil, Pair (Number (Int 3), Nil))), Nil)  *)
  | Pair (Symbol "let", Pair(pram_lst , body)) -> (tag_parse_expression (let_expantion pram_lst body ))
  (* let-star-expantion *)
  | Pair(Symbol "let*", Pair(param_lst, body)) -> (tag_parse_expression (letStar_expantion param_lst body)) 
  | Pair(Symbol "letrec", Pair(param_lst, body)) -> (tag_parse_expression (letRec_expantion param_lst body))

  (* define-mit-expantion *)
  | Pair(Symbol("define"), Pair(Pair(Symbol(var_name), args_list), body)) -> 
    (tag_parse_expression (Pair(Symbol "define", Pair(Symbol(var_name), Pair(Pair(Symbol("lambda"), Pair(args_list, body)), Nil)))))


  (* Constant parser *)
  | Bool(_) -> Const(Sexpr(sexpr))
  | Char(_) -> Const(Sexpr(sexpr))
  | Number(_) -> Const(Sexpr(sexpr))
  | String(_) -> Const(Sexpr(sexpr))
  | TagRef(_) -> Const(Sexpr(sexpr))
  | Pair (Symbol ("quote"), cdr) -> 
    (match cdr with 
      | Pair(something, Nil) -> Const(Sexpr(something))
      | _ -> Const(Sexpr(cdr)))
  | TaggedSexpr(name, tag_value) -> 
    (match tag_value with
      | Pair (Symbol ("quote"), cdr) -> 
        (match cdr with 
          | Pair(something, Nil) -> Const(Sexpr(TaggedSexpr(name, something)))
          | _ -> Const(Sexpr(TaggedSexpr(name, cdr))))
      | _ -> Const(Sexpr(TaggedSexpr(name, tag_value))))


  (* Variable parser *)
  | Symbol(name) -> 

  if (List.mem name reserved_word_list) then raise (X_this_shouldnt_happen_error name) else Var(name)

  (* If-expression parser *)
  | Pair(Symbol("if"), if_sexp) ->
    (match if_sexp with
    | Pair(test_sexp, Pair(dit_sexp, maybe_dif_sexp)) -> 
      let test = (tag_parse_expression test_sexp) in
      let dit = (tag_parse_expression dit_sexp) in
      let dif = 
        (match maybe_dif_sexp with
          | Pair(dif_sexp, Nil) -> (tag_parse_expression dif_sexp) 
          | Nil -> Const(Void)
          | _ -> raise (X_syntax_error "from if")) in
      If(test, dit, dif)
    | _ -> raise (X_syntax_error "from if"))

  (* Lambda-expression parser *)
  | Pair(Symbol("lambda"), Pair(arg_list, exprs)) -> 
    (match exprs with
    | Nil -> raise (X_syntax_error "empty body in lambda")
    | _ ->
    (let body = tag_parse_expression (Pair(Symbol("begin"), exprs)) in
    (match arg_list with
    | Symbol(variadic_symbol) -> LambdaOpt([], variadic_symbol, body)
    | Pair(_, _) ->
      (let is_simple = (is_simple_arg_list arg_list) in
      let arg_list = (get_names_from_symbol_list arg_list) in
      let vs_at_front_arg_list = last_to_front arg_list in
      if (is_simple) 
      then LambdaSimple(arg_list, body) 
      else LambdaOpt((List.tl vs_at_front_arg_list), (List.hd vs_at_front_arg_list), body))
    | Nil -> LambdaSimple([], body)
    | _ -> raise (X_syntax_error "from lambda2"))))

  (* Or-expression parser *)
  | Pair (Symbol("or"), args) -> ( match args with 
                                  | Nil ->  Const(Sexpr(Bool(false)))
                                  | Pair(sexp, Nil) -> (tag_parse_expression sexp)
                                  | _-> Or (tag_parse_expressions (flatten (args))))

  

  (* Set-expression parser *)
  | Pair (Symbol("set!"), var_val_sexp) ->  
    (match var_val_sexp with
      | Pair(var_sexp, Pair(val_sexp, Nil))-> Set (tag_parse_expression (var_sexp),
                                                          tag_parse_expression (val_sexp))
      | _ -> raise (X_syntax_error "")(*raise X_syntax_error "from set!" *) )

  (* Define-expression parser *)
  | Pair (Symbol("define"), var_val_sexp) -> 
    (match var_val_sexp with
      | Pair(var_sexp, value_sexp)-> 
        (let var_exp =  (tag_parse_expression (var_sexp)) in
        (match var_exp with 
        | Var(x) -> Def (var_exp, match value_sexp with | Pair(val_sexp, Nil) -> tag_parse_expression (val_sexp) | Nil -> Const(Void) | _ -> raise (X_syntax_error "from define"))
        | _ -> raise (X_syntax_error "from define")))
      | _ -> raise (X_syntax_error "from define"))

  (* Sequence-expression parser *)
  | Pair(Symbol("begin"), sexprs) ->
    (match sexprs with
    | Pair(first, rest) -> (match rest with
                          | Nil -> (tag_parse_expression first)
                          | Pair(_, _) -> (Seq(tag_parse_expressions (flatten sexprs)))
                          | _ -> raise (X_this_shouldnt_happen_error "from begin"))
    | Nil -> Const(Void)
    | _ -> raise (X_syntax_error "from begin")) (* thought that through - (begin . 1) is not legal thus the sexprs cannot be not a pair nor a Nil *)

  (* Application-expression parser *)
  (*Pair (Pair (Symbol "lambda", Pair (Nil, Pair (Number (Int 3), Nil))), Nil)
       Pair(Symbol "+", Pair(Number (Int 1), Pair(Number (Int 2), Nil)))   *)
  | Pair (first, rest) -> 
    let op = 
      (match first with 
      | Symbol(op) -> 
        if (List.mem op reserved_word_list) 
        then raise (X_this_shouldnt_happen_error "from applic")(* we were supposed to parse all the reserved words containing expressions *)
        else (tag_parse_expression first)
      | _ -> (tag_parse_expression first)) in
      let args =(match rest with
                  | Nil -> []
                  | _->  (tag_parse_expressions (flatten rest))) in
      Applic(op, args)
  
  (* All parser failed  *)
  | _ -> raise (X_lambda_error sexpr)


and tag_parse_expressions sexprs = 
(List.map tag_parse_expression sexprs) 
;;

  
end;; (* struct Tag_Parser *)
 
 open Tag_Parser;;

 let test_string code =
let sexpr = (Reader.read_sexpr code) in (tag_parse_expression sexpr);;

    
