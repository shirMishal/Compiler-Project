#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

exception X_this_shouldnt_happen_error;;

let rec find x lst =
    match lst with
    | [] -> raise (X_this_shouldnt_happen_error)
    | h :: t -> if x = h then 0 else 1 + find x t

let rec tag_bound_or_free var_name bound_lists deep =
  match bound_lists with
  | [] -> Var' (VarFree (var_name))
  | bound_0_list :: rest_bound_lists -> if (List.mem var_name bound_0_list) then Var'(VarBound(var_name , deep ,(find var_name bound_0_list))) else (tag_bound_or_free var_name rest_bound_lists (deep +1))

let rec lexical expr params_bound_lists =
match expr with
| Const (constant) -> Const'(constant)
| If (test_expr , then_expr , else_expr) -> If'( (lexical test_expr params_bound_lists), ( lexical then_expr params_bound_lists), (lexical else_expr params_bound_lists))
| Seq (expr_list) -> Seq'(List.map (fun expr -> (lexical expr params_bound_lists)) expr_list)
| Set (var_expr, val_expr) -> Set'((lexical var_expr params_bound_lists), (lexical val_expr params_bound_lists))
| Def (var_expr, val_expr) -> Def'((lexical var_expr params_bound_lists), (lexical val_expr params_bound_lists))
| Or (expr_list) -> Or'(List.map (fun expr -> (lexical expr params_bound_lists)) expr_list)
| Applic (op_expr, args_expr_list) -> Applic' ((lexical op_expr params_bound_lists) , List.map (fun expr -> (lexical expr params_bound_lists)) args_expr_list)
| Var (var_name) ->( match params_bound_lists with
                    | [] -> Var'(VarFree(var_name))
                    | param_list :: bound_lists ->  if (List.mem var_name param_list) then Var'(VarParam(var_name , (find var_name param_list))) else (tag_bound_or_free var_name bound_lists 0)
                    )
| LambdaSimple (arg_list , body_expr) -> LambdaSimple' (arg_list, (lexical body_expr (arg_list :: params_bound_lists)))
| LambdaOpt (arg_list , optional_arg ,body_expr) -> LambdaOpt' (arg_list , optional_arg, (lexical body_expr ((arg_list@[optional_arg]) :: params_bound_lists)))                                                                      


let annotate_lexical_addresses e = lexical e [];;

let annotate_tail_calls e = raise X_not_yet_implemented;;

let box_set e = raise X_not_yet_implemented;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
