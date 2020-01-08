#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)

  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
(*
let rem_dup_from_right lst =
  let rec is_member n mlst =
    match mlst with
    | [] -> false
    | h::tl ->
        begin
          if h=n then true
          else is_member n tl
        end
  in
  let rec loop lbuf =
    match lbuf with
    | [] -> []
    | h::tl ->
        begin
        let rbuf = loop tl
        in
          if is_member h rbuf then rbuf
          else h::rbuf
        end
  in
  loop lst;;
*)
exception X_this_shouldnt_happen_error of string;;

let rec find x lst =
    match lst with
    | [] -> raise (X_this_shouldnt_happen_error "from find")
    | h :: t -> if x = h then 0 else 1 + find x t
;;
let rec copy_no_dup list_to_return list_to_copy=
match list_to_copy with
| [] -> list_to_return
| hd :: tl -> if List.mem hd list_to_return then (copy_no_dup list_to_return tl) else (copy_no_dup (list_to_return@[hd]) tl)
;;
let rem_dup lst = 
match lst with
| []-> []
| hd::tl -> (match tl with 
            | []-> lst
            | car_tl:: cdr_tl -> copy_no_dup [hd] tl);;


module SS = Set.Make(String);;



let make_free_var_table ast_expr' =
let offset_counter = ref 0 in
let set_of_names = make_free_var_set SS.empty ast_expr' in
let list_of_names = SS.elements set_of_names in
  (List.map 
    (fun name ->
      let old_count = !offset_counter in
        offset_counter:= !offset_counter + 8;
        (name, old_count)) 
    list_of_names);;



let rec make_free_var_set current_set_of_names ast_expr' = 
let make_set_local = (make_free_var_set current_set_of_names) in
SS.union current_set_of_names (match ast_expr' with
| Var'(VarFree(var_name)) -> (SS.add var_name current_set_of_names)
| Applic'(op, arg_list) -> (SS.union (make_set_local op) (List.fold_left SS.union SS.empty (map make_set_local arg_list)))
| ApplicTP'(op, arg_list) -> (SS.union (make_set_local op) (List.fold_left SS.union SS.empty (map make_set_local arg_list)))
| If'(test, dit, dif) -> (SS.union (make_set_local test) (SS.union (make_set_local dit) (make_set_local dif)))
| Seq'(expr'_list) -> (List.fold_left SS.union SS.empty (map make_set_local expr'_list))
| Set'(Var'(var_expr'), value) -> (SS.union 
                                    (match var_expr' with
                                      | VarFree(variable) -> (SS.singleton variable)
                                      | _ -> SS.empty)
                                    (make_set_local value))
| Def'(Var'(VarFree(variable)), value) -> (SS.union (SS.singleton variable) (make_set_local value))
| Or'(expr'_list) -> (List.fold_left SS.union SS.empty (map make_set_local expr'_list))
| LambdaSimple'(_, body) -> (make_set_local body)
| LambdaOpt'(_, _, body) -> (make_set_local body)
| BoxSet'(_, expr') -> (make_set_local expr')
| _ -> SS.empty);;



let rec make_sexpr_list ast_expr' = (*returns list of all sexprs in const *)
match ast_expr' with
  | Const'(constant) -> [constant]
  | Var' (var) -> []
  | Applic' (op_expr' , args_expr'_list) -> List.flatten ((make_sexpr_list op_expr') :: List.map (fun expr' -> make_sexpr_list expr') args_expr'_list)
  | ApplicTP' (op_expr' , args_expr'_list) -> List.flatten ((make_sexpr_list op_expr') :: List.map (fun expr' -> make_sexpr_list expr') args_expr'_list)
  | If' (test_expr' , then_expr' , else_expr') -> List.flatten [(make_sexpr_list test_expr') ;(make_sexpr_list then_expr' ) ;(make_sexpr_list else_expr')]
  | Seq' (expr'_list) -> (match expr'_list with 
                        | []-> []
                        | _ -> List.flatten ( List.map (fun expr' -> make_sexpr_list expr') expr'_list)
                        )
  | Set' (var_expr', val_expr') -> List.flatten [(make_sexpr_list var_expr'); (make_sexpr_list val_expr')]
  | Def' (var_expr', val_expr') -> List.flatten [(make_sexpr_list var_expr'); (make_sexpr_list val_expr')]
  | Or'(expr'_list) -> (match expr'_list with 
                        | []-> []
                        | _ -> List.flatten ( List.map (fun expr' -> make_sexpr_list expr') expr'_list)
                        )
  | LambdaSimple' (param_list , body_expr') -> make_sexpr_list body_expr'
  | LambdaOpt' (param_list , param_opt , body_expr') -> make_sexpr_list body_expr'
  | BoxSet'(var, expr) -> make_sexpr_list expr
  | BoxGet'(var) -> []
  | Box'(var) -> []
  ;;
  
  let is_not_obligatory sexpr = 
  match sexpr with
  | Void -> false
  | Sexpr(Bool(_))-> false
  | Sexpr(Nil) -> false
  | _ -> true
  ;;

  let rec make_list_with_sub sexpr = 
  match sexpr with 
  | Sexpr (Pair ( hd_sexpr, tl_sexpr)) -> (make_list_with_sub (Sexpr(tl_sexpr)))@ [Sexpr (Pair ( hd_sexpr, tl_sexpr))]
  | Sexpr (TaggedSexpr (string , sexpr)) -> (make_list_with_sub (Sexpr (sexpr)))@[Sexpr (TaggedSexpr (string , sexpr))]
  | Sexpr (Symbol (sym_name)) -> [Sexpr (String (sym_name))]@[Sexpr (Symbol (sym_name))]
  | Sexpr (s) -> [Sexpr (s)] 
  | Void -> [] (*this should not happen*)
  ;;

  let add_sub_sexpr sexpr_list = List.flatten (List.map (fun sexpr->  make_list_with_sub sexpr) sexpr_list);;
  (*let add_sub_sexpr sexpr_list = List.flatten (List.map (fun sexpr-> (match sexpr with 
                                                                      | Sexpr(s) -> make_list_with_sub sexpr
                                                                      | _ -> raise X_this_should_not_happen)) sexpr_list);;*)
  
 



  let make_sexpr_lists asts = (*returns list contains sexprs for all asts with sub sexpr with no dup with no obligatory*)
  (*let asts_renamed = rename_refs asts in*)
  let list_of_sexpr_lists =  List.map make_sexpr_list asts_renamed in
  let list_of_all_sexpr = List.flatten list_of_sexpr_lists in
  let set_of_all_sexpr = rem_dup list_of_all_sexpr in (*flat list with no dup of all sexpr *)
  let set_of_all_sexpr = List.filter is_not_obligatory set_of_all_sexpr in
  let list_with_sub_sexpr = add_sub_sexpr set_of_all_sexpr in
  let set_of_all_sexpr = rem_dup list_with_sub_sexpr in
  let set_of_all_sexpr = List.filter is_not_obligatory set_of_all_sexpr in
  set_of_all_sexpr
  ;;

let rec find_offset name_str const_tbl =
match const_tbl with
| [] -> raise (X_this_shouldnt_happen_error "")
| _-> 1
;;

  let rec make_tuples sexpr_list offset const_tbl=
  match sexpr_list with
  | [] -> const_tbl
  | hd:: tl -> (match hd with 
                | Sexpr(Number(Int (integer)))-> make_tuples tl (offset +9) (const_tbl@[(Sexpr(Number(Int (integer))),(offset,"MAKE_LITERAL_INT("^(string_of_int integer)^")" ))])
                | Sexpr(Number(Float (float)))-> make_tuples tl (offset +9) (const_tbl@[(Sexpr(Number (Float (float))),(offset,"MAKE_LITERAL_FLOAT("^(string_of_float float)^")" ))])
                | Sexpr (Char (char)) -> make_tuples tl (offset +2) (const_tbl@[(Sexpr(Char (char))),(offset,"MAKE_LITERAL_CHAR('"^(Char.escaped char)^"')" ))])
                | Sexpr (String (string)) -> make_tuples tl (offset+ (String.length string) +9) (const_tbl@[Sexpr (String (string)),(offset,"MAKE_LITERAL_STRING "^(string_of_int (String.length string))^ " '" ^ string ^"'" ))])
                | Sexpr (Symbol (name_str)) -> make_tuples tl (offset +9) (const_tbl@[Sexpr (Symbol (name_str)),(offset,"MAKE_LITERAL_SYMBOL(consts+"^(string_of_int (find_offset name_str (List.rev const_tbl)))^")" ))])
                | _-> raise X_this_should_not_happen
                )
  ;;
(*| Bool of bool
  | Nil
  | Number of tuple
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;
*)
  let add_obligatory lst = 
  let obligatory = [(Sexpr Nil, (0,"MAKE_NIL")); (Void, (1,"MAKE_VOID")); (Sexpr (Bool true), (2 ,"MAKE_BOOL(1)")) ; (Sexpr (Bool false), (4 ,"MAKE_BOOL(0)"))] in
  obligatory@lst;;

  let make_list_for_consts_tbl asts = add_obligatory (make_tuples (make_sexpr_lists asts) 6 []);;

  let make_consts_tbl asts = make_list_for_consts_tbl asts;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

