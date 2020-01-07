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
  val rename_refs : expr' list -> expr' list 
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
  
  let rename_refs asts = 
  let taged_list = ref [] in
  let acc_to_index = ref 0 in
  let counter = ref (-1) in
  let rec rename_ref_sexpr sexpr =
  (match sexpr with
    | Pair (first_sexpr , sec_sexpr) -> Pair ((rename_ref_sexpr first_sexpr) , (rename_ref_sexpr sec_sexpr))
    | TaggedSexpr (string , sexpr) -> if List.mem string !taged_list 
                                    then (TaggedSexpr (string^(string_of_int ((find string !taged_list)+ !acc_to_index)) , (rename_ref_sexpr sexpr))) 
                                    else (taged_list:= !taged_list@[string] ; counter:= !counter+1 ; let tag = !counter in (TaggedSexpr (string^(string_of_int tag) , (rename_ref_sexpr sexpr))))
    | TagRef (string) -> if List.mem string !taged_list 
                        then (TagRef(string^(string_of_int ((find string !taged_list)+ !acc_to_index)))) 
                        else (taged_list:= !taged_list@[string] ; counter:= !counter+1 ; TagRef(string^(string_of_int !counter)))
    | _ -> sexpr
  )in
  let rec rename_ref ast =
  acc_to_index:= !acc_to_index +(List.length !taged_list) ;
  taged_list:= [] ; 
  (match ast with 
    (*| Const' (Sexpr (TaggedSexpr (string , sexpr))) -> if List.mem string !taged_list then Const' (Sexpr (TaggedSexpr (string^(string_of_int (find string !taged_list)) , (rename_ref_sexpr sexpr)))) else taged_list:= !taged_list@[string] ; counter:= !counter+1 ; Const' (Sexpr (TaggedSexpr (string^(string_of_int !counter) , (rename_ref_sexpr sexpr))))*)
    | Const' (Sexpr (sexpr)) -> Const' (Sexpr (rename_ref_sexpr sexpr)) 
    | Applic' (op_expr' , args_expr'_list) -> Applic' ((rename_ref op_expr') , (List.map rename_ref args_expr'_list))
    | ApplicTP' (op_expr' , args_expr'_list) -> ApplicTP' ((rename_ref op_expr') , (List.map rename_ref args_expr'_list))
    | If' (test_expr' , then_expr' , else_expr') -> If' ((rename_ref test_expr') , (rename_ref then_expr') ,(rename_ref else_expr'))
    | Seq' (expr'_list) -> (match expr'_list with 
                          | []-> ast
                          | _ -> Seq' (List.map rename_ref expr'_list) 
                          )
    | Set' (var_expr', val_expr') -> Set' (var_expr', (rename_ref val_expr'))
    | Def' (var_expr', val_expr') -> Def' (var_expr', (rename_ref val_expr'))
    | Or'(expr'_list) -> (match expr'_list with 
                          | []-> ast
                          | _ -> Or' (List.map rename_ref expr'_list )
                          )
    | LambdaSimple' (param_list , body_expr') -> LambdaSimple' (param_list , (rename_ref body_expr'))
    | LambdaOpt' (param_list , param_opt , body_expr') -> LambdaOpt' (param_list , param_opt , (rename_ref body_expr'))
    | BoxSet'(var, expr) -> BoxSet'(var, (rename_ref expr))
    | _ -> ast
  ) in
  let mapped_asts = List.map (fun ast -> rename_ref ast) asts in
  mapped_asts;;



  let make_sexpr_lists asts = (*returns list contains sexprs for all asts with sub sexpr with no dup with no obligatory*)
  let asts_renamed = rename_refs asts in
  let list_of_sexpr_lists =  List.map make_sexpr_list asts_renamed in
  let list_of_all_sexpr = List.flatten list_of_sexpr_lists in
  let set_of_all_sexpr = rem_dup list_of_all_sexpr in (*flat list with no dup of all sexpr *)
  let set_of_all_sexpr = List.filter is_not_obligatory set_of_all_sexpr in
  let list_with_sub_sexpr = add_sub_sexpr set_of_all_sexpr in
  let set_of_all_sexpr = rem_dup list_with_sub_sexpr in
  let set_of_all_sexpr = List.filter is_not_obligatory set_of_all_sexpr in
  set_of_all_sexpr
  ;;

  let make_tuples sexpr_list offset const_tbl=
  match sexpr_list with
  | [] -> const_tbl
  | hd:: tl -> (match hd with 
                | Sexpr(Number(Int (integer)))-> make_tuples tl (offset +9) (const_tbl@[(Sexpr(Number(Int (integer))),(offset,"MAKE_LITERAL_INT("^(string_of_int integer)^")" ))])
                | Sexpr(Number(Float (float)))-> make_tuples tl (offset +9) (const_tbl@[(Sexpr(Float(Int (float))),(offset,"MAKE_LITERAL_FLOAT("^(string_of_float float)^")" ))])
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

