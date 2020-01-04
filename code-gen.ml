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
(*code from stackOverflow https://stackoverflow.com/questions/30634119/ocaml-removing-duplicates-from-a-list-while-maintaining-order-from-the-right*)
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

  let rec make_list_with_sub (Sexpr(s)) = 
  match s with 
  | Pair ( hd_sexpr, tl_sexpr) -> [make_list_with_sub tl_sexpr]@ [Sexpr (Pair ( hd_sexpr, tl_sexpr))]
  | TaggedSexpr (string , sexpr) -> [make_list_with_sub sexpr]@[Sexpr (TaggedSexpr (string , sexpr))]
  | _ -> [s] 
  ;;

  let add_sub_sexpr sexpr_list = List.flatten (List.map (fun sexpr-> (match sexpr with 
                                                                      | Sexpr(s) -> make_list_with_sub sexpr
                                                                      | _ -> raise X_this_should_not_happen)) sexpr_list);;
  
  let make_sexpr_lists asts = (*returns list of lists contains sexpr for each ast*)
  let list_of_sexpr_lists =  List.map make_sexpr_list asts in
  let list_of_all_sexpr = List.flatten list_of_sexpr_lists in
  let set_of_all_sexpr = rem_dup_from_right list_of_all_sexpr in (*flat list with no dup of all sexpr *)
  let set_of_all_sexpr = List.filter is_not_obligatory set_of_all_sexpr in
  let list_with_sub_sexpr = add_sub_sexpr set_of_all_sexpr in
  let set_of_all_sexpr = rem_dup_from_right list_with_sub_sexpr in
  let set_of_all_sexpr = List.filter is_not_obligatory set_of_all_sexpr in
  set_of_all_sexpr
  ;;


  let add_obligatory lst = 
  let obligatory = [(Void, (0,"SOB_VOID")); (Sexpr Nil, (1,"SOB_NIL")); (Sexpr (Bool false), (2,"SOB_FALSE"));(Sexpr (Bool true), (4,"SOB_TRUE"))] in
  obligatory@lst;; (*add update to lst offset values *)

  let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

(*| Sexpr (Number(tuple)) -> 
  | Sexpr (Char (char)) ->
  | Sexpr (String (string)) ->
  | Sexpr (Symbol (string)) ->
  | Sexpr (Pair ( hd_sexpr, tl_sexpr)) ->
  | Sexpr (TaggedSexpr (string , sexpr)) -> 
  | Sexpr (TagRef (string)) ->*)
 