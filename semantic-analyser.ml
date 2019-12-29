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
  val test : string -> expr'
end;;

module Semantics : SEMANTICS = struct

exception X_this_shouldnt_happen_error;;

let rec find x lst =
    match lst with
    | [] -> raise (X_this_shouldnt_happen_error)
    | h :: t -> if x = h then 0 else 1 + find x t
;;
let rec tag_bound_or_free var_name bound_lists deep =
  match bound_lists with
  | [] -> Var' (VarFree (var_name))
  | bound_0_list :: rest_bound_lists -> if (List.mem var_name bound_0_list) then Var'(VarBound(var_name , deep ,(find var_name bound_0_list))) else (tag_bound_or_free var_name rest_bound_lists (deep +1))
;;

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
;;

(*let is_tp_or  expr'_list expr' is_tp = if List.nth expr'_list ((List.length expr'_list)-1)= expr' then is_tp else false;;*)
let get_last_element list = List.hd (List.rev list);;
let get_all_except_last list = List.rev (List.tl (List.rev list));;

let rec tail_call expr' is_tp =
match expr' with
  | Const'(constant) -> Const'(constant)
  | Var' (var) -> Var' (var)
  | Applic' (op_expr' , args_expr'_list) -> if is_tp then ApplicTP'((tail_call op_expr' false), (List.map (fun expr'-> (tail_call expr' false)) args_expr'_list))
                                                     else Applic'((tail_call op_expr' false), (List.map (fun expr'-> (tail_call expr' false)) args_expr'_list))
  | If' (test_expr' , then_expr' , else_expr') -> If' ((tail_call test_expr' false) , (tail_call then_expr' is_tp) , (tail_call else_expr' is_tp))
  | Seq' (expr'_list) -> (match expr'_list with 
                        | []-> Seq'(expr'_list)
                        | expr'::[] -> Seq'([tail_call expr' is_tp])
                        | _ -> Seq'( (List.map (fun expr'-> (tail_call expr' false)) (get_all_except_last expr'_list))@[(tail_call (get_last_element expr'_list) is_tp)])
                        )
  | Set' (var_expr', val_expr') -> Set'(var_expr', (tail_call val_expr' false))
  | Def' (var_expr', val_expr') -> Def' (var_expr', (tail_call val_expr' false))
  | Or'(expr'_list) -> (match expr'_list with 
                        | []-> Or'(expr'_list)
                        | expr'::[] -> Or'([tail_call expr' is_tp])
                        | _ -> Or'( (List.map (fun expr'-> (tail_call expr' false)) (get_all_except_last expr'_list))@[(tail_call (get_last_element expr'_list) is_tp)])
                        )
  | LambdaSimple' (param_list , expr') -> LambdaSimple'(param_list , ( tail_call expr' true))
  | LambdaOpt' (param_list , param_opt , expr') -> LambdaOpt' (param_list , param_opt , ( tail_call expr' true))
  
  | _ -> raise X_syntax_error
  ;;

let merge_get_set list = List.fold_left (fun (curr_get, curr_set) (acc_get, acc_set) -> (curr_get @ acc_get, curr_set @ acc_set)) ([],[]) list;;

(*make the boxing*)
let apply_box params_list body_expr' = raise X_not_yet_implemented;;


let counter = ref 0;;
(*returns (list of get appearance of param , list of set appearance of param)*)
let rec check_get_set param_string body_expr' (get_list, set_list) = 
match body_expr' with
  | Const'(constant) -> (get_list, set_list)
  | Var' (var) -> (match var with 
                  | VarParam (param_string , _) -> ([!counter] :: get_list, set_list )
                  | VarBound (param_string , _, _) -> ([!counter] :: get_list, set_list )
                  | _ -> (get_list, set_list))
  | Set' (var_expr', val_expr') ->( match var_expr' with 
                    | Var' (VarParam (param_string , _)) -> (get_list, [!counter] :: set_list )
                    | Var' (VarBound (param_string , _,_)) -> (get_list, [!counter] :: set_list )
                    | _ -> (get_list, set_list))
  | Applic' (op_expr' , args_expr'_list) -> (let get_set_in_args = List.map (fun arg -> (check_get_set param_string arg ([], [])) ) args_expr'_list in
                                            let get_set_in_op = (check_get_set param_string op_expr' ([], [])) in
                                            let get_set_lists = (get_set_in_op :: get_set_in_args) in
                                            let get_set = merge_get_set get_set_lists in 
                                            get_set)(*not sure if needs to check for special case of lambda in args *)
  (*| ApplicTP' (op_expr' , args_expr'_list) -> *)
  | If' (test_expr' , then_expr' , else_expr') -> (check_get_set param_string (Seq'([test_expr' ; then_expr' ; else_expr'])) (get_list, set_list))
  | Seq' (expr'_list) -> (match expr'_list with 
                        | []-> (get_list, set_list)
                        (* expr'::[] -> Seq'([boxing expr' ])*)
                        | _ -> (get_list, set_list)
                        )
    (*not allowed | Def' (var_expr', val_expr') -> *)
  (*
  | Or'(expr'_list) -> (match expr'_list with 
                        | []-> 
                        (* expr'::[] -> Or'([tail_call expr' is_tp])*)
                        | _ -> 
                        )
  *)
  | LambdaSimple' (param_list , body) -> (if (List.mem param_string param_list) 
                                                then (get_list, set_list) 
                                                else (begin
                                                      counter := !counter +1;
                                                      check_get_set param_string body (get_list, set_list)
                                                     end)
                                          )
  (*
  | LambdaOpt' (param_list , param_opt , body_expr') -> 
  *)
  | _ -> raise X_syntax_error
(*raise X_not_yet_implemented*)
;;

(*returns true if get & set do not share same rib - means we should box*)
let check_lists_unshared_rib get_list set_list = 
let ancestors_get = List.map (fun ancestor_lst -> List.hd ancestor_lst) get_list in
let ancestors_set = List.map (fun ancestor_lst -> List.hd ancestor_lst) set_list in
(ormap (fun ancestor_get -> (ormap (fun ancestor_set -> if (ancestor_set = ancestor_get) then false else true )  ancestors_set)
        )
        ancestors_get);;


type had_read_write = 
| R
| W
| RW
| NOTHING;;

let rw_union rep_list =
  let rw_union_two rep1 rep2 =
  (match rep1 with
  | RW -> RW
  | NOTHING -> rep2
  | _ -> if (rep1 == rep2) then rep1 else RW) in
(List.fold_left rw_union_two NOTHING rep_list);;
 
let rec report_read_write (param:string) curr_expr' = 
match curr_expr' with
| If'(test, dit, dif) -> 
  let rep_test = (report_read_write param test) in
  let rep_dit = (report_read_write param dit) in
  let rep_dif = (report_read_write param dif) in
  (rw_union [rep_dif; rep_dit; rep_test])
| Seq'(expr'_list) -> (rw_union (map (report_read_write param) expr'_list))
| Set'(name_var, value) -> 
  let this_set = match name_var with | Var'(VarBound(name, mac, min)) -> if (name == param) then W else NOTHING | _ -> NOTHING in
  (rw_union [this_set; (report_read_write param value)])
| Or'(expr'_list) -> (rw_union (map (report_read_write param) expr'_list))
| LambdaSimple'(param_list, body) -> if (List.mem param param_list) then NOTHING else (report_read_write param body)
| LambdaOpt'(param_list, opt_param, body) -> (if ((opt_param == param) || (List.mem param param_list)) then NOTHING else (report_read_write param body))
| Applic'(operator, operand_list) -> (rw_union ([(report_read_write param operator)]@ (map (report_read_write param) operand_list)))
| ApplicTP'(operator, operand_list) -> (rw_union ([(report_read_write param operator)]@ (map (report_read_write param) operand_list)))
| Var'(VarBound(name, mac, mic)) -> (if (name == param) then R else NOTHING);;

let check_problems list_reports = 
let reads = (List.filter (fun rep -> rep == R) list_reports) in 
let writes = (List.filter (fun rep -> rep == W) list_reports) in
let read_writes = (List.filter (fun rep -> rep == RW) list_reports) in
if ((List.length read_writes) > 1)
then true
else
  if ((List.length read_writes) == 1)
  then
    if (((List.length reads) == 0) && ((List.length writes) == 0))
    then false
    else true
  else
    if (((List.length reads) > 0) && ((List.length writes) > 0))
    then true
    else false
;;


let rec get_report_list param body_expr' =
match body_expr' with
| If'(test, dit, dif) -> 
  let rep_test = (get_report_list param test) in
  let rep_dit = (get_report_list param dit) in
  let rep_dif = (get_report_list param dif) in
  (rep_dif@ rep_dit@ rep_test)
| Seq'(expr'_list) -> 
  let report_lists = (map (get_report_list param) expr'_list) in
  let complete_list = (List.fold_left (fun a b -> a@ b) [] report_lists) in
  complete_list
| Set'(name_var, value) -> 
  let this_set = match name_var with | Var'(VarBound(name, mac, min)) -> if (name == param) then [W] else [] | _ -> [] in
  (get_report_list param value)@ this_set
| Or'(expr'_list) -> 
  let report_lists = (map (get_report_list param) expr'_list) in
  let complete_list = (List.fold_left (fun a b -> a@ b) [] report_lists) in
  complete_list
| LambdaSimple'(param_list, body) -> if (List.mem param param_list) then [NOTHING] else [(report_read_write param body)]
| LambdaOpt'(param_list, opt_param, body) -> if ((opt_param == param) || (List.mem param param_list)) then [NOTHING] else [(report_read_write param body)]
| Applic'(operator, operand_list) -> 
  let report_lists = (map (get_report_list param) operand_list) in
  let complete_list = (List.fold_left (fun a b -> a@ b) [] report_lists) in
  complete_list@ (get_report_list param operator)
| ApplicTP'(operator, operand_list) -> 
  let report_lists = (map (get_report_list param) operand_list) in
  let complete_list = (List.fold_left (fun a b -> a@ b) [] report_lists) in
  complete_list@ (get_report_list param operator)
| Var'(VarParam(name, mic)) -> (if (name == param) then [R] else [])
;;

let should_box param body_expr' = 
(check_problems (get_report_list param body_expr'))
              

(*returns new boxes body if needed *)
let rec box_lambda_simple  param_list body_expr' = 
  let params_need_boxing = List.filter (fun param -> should_box param body_expr') param_list in
  match params_need_boxing with
  | [] -> body_expr'
  | _ -> apply_box params_need_boxing body_expr'
  ;;

let rec box_lambda_opt  param_list param_opt body_expr' = raise X_not_yet_implemented;;

let rec boxing expr' =
match expr' with
  | Const'(constant) -> Const'(constant)
  | Var' (var) -> Var' (var)
  | Applic' (op_expr' , args_expr'_list) -> Applic' ((boxing op_expr') , List.map (fun expr' -> boxing expr') args_expr'_list)
  | ApplicTP' (op_expr' , args_expr'_list) -> ApplicTP' ((boxing op_expr') , List.map (fun expr' -> boxing expr') args_expr'_list)
  | If' (test_expr' , then_expr' , else_expr') -> If' ((boxing test_expr') , (boxing then_expr' ) , (boxing else_expr'))
  | Seq' (expr'_list) -> (match expr'_list with 
                        | []-> Seq'(expr'_list)
                        (* expr'::[] -> Seq'([boxing expr' ])*)
                        | _ -> Seq'( List.map (fun expr' -> boxing expr') expr'_list)
                        )
  | Set' (var_expr', val_expr') -> Set'(var_expr', (boxing val_expr'))
  | Def' (var_expr', val_expr') -> Def'(var_expr', (boxing val_expr'))
  | Or'(expr'_list) -> (match expr'_list with 
                        | []-> Or'(expr'_list)
                        (* expr'::[] -> Or'([tail_call expr' is_tp])*)
                        | _ -> Or'( List.map (fun expr' -> boxing expr') expr'_list)
                        )
  | LambdaSimple' (param_list , body_expr') -> LambdaSimple'(param_list ,(boxing ( box_lambda_simple  param_list body_expr')) )
  | LambdaOpt' (param_list , param_opt , body_expr') -> LambdaOpt' (param_list , param_opt ,(boxing ( box_lambda_opt  param_list param_opt body_expr')))
  
  | _ -> raise X_syntax_error
  ;;


let annotate_lexical_addresses e = lexical e [];;

let annotate_tail_calls e = tail_call e false;;

let box_set e = boxing e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  

let test string = string;; 

end;; (* struct Semantics *)
