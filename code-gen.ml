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
(*val make_constant_lists : expr' list -> constant*)
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
exception X_print_sexpr of sexpr

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

let pointer_length = 8;;
let number_object_length = 9;;
let symbol_object_length = 9;;
let string_object_length = 9;;
let char_object_length = 2;;


let primitive_vars = 
  [("boolean?", 0); ("float?", 1); ("integer?", 2); ("pair?", 3);
   ("null?", 4); ("char?", 5); ("string?", 6);
   ("procedure?", 7); ("symbol?", 8); ("string-length", 9);
   ("string-ref", 10); ("string-set!", 11); ("make-string", 12);
   ("symbol->string", 13); 
   ("char->integer", 14); ("integer->char", 15); ("eq?", 16);
   ("+", 17); ("*", 18);( "-", 19); ("/", 20); ("<", 21); ("=", 22)
(* you can add yours here *)];;

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

let make_free_var_table asts =
let offset_counter = ref 23 in
let list_of_set_of_names = (map (make_free_var_set SS.empty) asts) in
let set_of_names = (List.fold_left SS.union SS.empty list_of_set_of_names) in
let list_of_names = SS.elements set_of_names in
  (List.map 
    (fun name ->
      let old_count = !offset_counter in
        offset_counter:= !offset_counter +1;
        (name, old_count)) 
    list_of_names);;

let tagged_expressions = ref [];;

let rec make_constants_list ast_expr' = (*returns list of all sexprs in const *)
match ast_expr' with
  | Const'(constant) -> (match constant with
                        | Void | Sexpr(Bool(_)) | Sexpr(Nil) -> []
                        | Sexpr(TaggedSexpr(name, value)) -> tagged_expressions:= (name, Sexpr(value)) :: !tagged_expressions ; [constant]
                        | _ -> [constant])
  | Var' (var) -> []
  | Applic' (op_expr' , args_expr'_list) -> List.flatten ((make_constants_list op_expr') :: List.map (fun expr' -> make_constants_list expr') args_expr'_list)
  | ApplicTP' (op_expr' , args_expr'_list) -> List.flatten ((make_constants_list op_expr') :: List.map (fun expr' -> make_constants_list expr') args_expr'_list)
  | If' (test_expr' , then_expr' , else_expr') -> List.flatten [(make_constants_list test_expr') ;(make_constants_list then_expr' ) ;(make_constants_list else_expr')]
  | Seq' (expr'_list) -> (match expr'_list with 
                        | []-> []
                        | _ -> List.flatten ( List.map (fun expr' -> make_constants_list expr') expr'_list)
                        )
  | Set' (var_expr', val_expr') -> List.flatten [(make_constants_list var_expr'); (make_constants_list val_expr')]
  | Def' (var_expr', val_expr') -> List.flatten [(make_constants_list var_expr'); (make_constants_list val_expr')]
  | Or'(expr'_list) -> (match expr'_list with 
                        | []-> []
                        | _ -> List.flatten (List.map (fun expr' -> make_constants_list expr') expr'_list)
                        )
  | LambdaSimple' (param_list , body_expr') -> make_constants_list body_expr'
  | LambdaOpt' (param_list , param_opt , body_expr') -> make_constants_list body_expr'
  | BoxSet'(var, expr) -> make_constants_list expr
  | BoxGet'(var) -> []
  | Box'(var) -> []
  ;;
  
  let is_not_obligatory constant = 
  match constant with
  | Void -> false
  | Sexpr(Bool(_))-> false
  | Sexpr(Nil) -> false
  | _ -> true
  ;;


  (* takes a constant <constant> and returnts a list of all constants which are sub-constant or equals to it *)
  let rec make_list_with_sub constant = 
  match constant with 
  | Void | Sexpr(Bool(_)) | Sexpr(Nil) -> []
  | Sexpr (Pair (hd_sexpr, tl_sexpr)) -> let car = (make_list_with_sub (Sexpr(hd_sexpr))) in
                                         let cdr = (make_list_with_sub (Sexpr(tl_sexpr))) in
                                         let all_pair =  (  [Sexpr (Pair(hd_sexpr, tl_sexpr))]) in
                                         car @ (cdr @ all_pair)
  | Sexpr (TaggedSexpr (string, sexpr_val)) -> tagged_expressions:= (string, Sexpr(sexpr_val)) :: !tagged_expressions ; (make_list_with_sub (Sexpr (sexpr_val))) @ [constant]
  | Sexpr (Symbol (sym_name)) -> [Sexpr (String (sym_name))]@[Sexpr (Symbol (sym_name))]
  | Sexpr (TagRef(name)) ->  [constant]
  | Sexpr (s) -> [constant]
  ;;

  let add_sub_sexpr sexpr_list = List.flatten (List.map (fun constant ->  make_list_with_sub constant) sexpr_list);;
  (*let add_sub_sexpr sexpr_list = List.flatten (List.map (fun constant-> (match constant with 
                                                                      | Sexpr(s) -> make_list_with_sub constant
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


  let make_constant_lists asts = (*returns list contains sexprs for all asts with sub constant with no dup with no obligatory*)
  let asts_renamed = (*rename_refs*) asts in
  let list_of_constants_lists =  List.map make_constants_list asts_renamed in
  let list_of_all_constants = List.flatten list_of_constants_lists in
  let set_of_all_constants = rem_dup list_of_all_constants in (*flat list with no dup of all constant *)
  let set_of_all_constants = add_sub_sexpr set_of_all_constants in
  rem_dup set_of_all_constants;;


let rec find_const_by_name name_to_find list = 
match list with
| [] -> raise (X_this_shouldnt_happen_error "from find const by name")
| hd::tl -> match hd with
            | (name, const) -> if (name = name_to_find) then const else (find_const_by_name name_to_find tl);;

let rec find_offset (const_to_find:constant) const_tbl =
let const_to_find = (match const_to_find with 
                    | Sexpr(TaggedSexpr(name, value)) -> Sexpr(value) 
                    | Sexpr(TagRef(name)) -> (find_const_by_name name !tagged_expressions)
                    | _ -> const_to_find) in
match const_tbl with
| [] -> 222222222222222
| hd::tl -> 
  match hd with
  | (const, (offset, _)) -> if const = const_to_find then offset else find_offset const_to_find tl;;

let replace_tagref const_tbl =
let update_tagref tuple = 
(match tuple with 
  | (Sexpr (Pair (TagRef (name1), TagRef (name2))) , (offset, asm_string )) -> (Sexpr (Pair (TagRef (name1), TagRef (name2))) , (offset, "MAKE_LITERAL_PAIR( const_tbl +" ^ (string_of_int (find_offset (find_const_by_name name1 !tagged_expressions) const_tbl)) ^ " , const_tbl +" ^ (string_of_int (find_offset (find_const_by_name name2 !tagged_expressions) const_tbl)) ^ ")" )) 
  | (Sexpr (Pair (TagRef (name1), other)) , (offset, asm_string )) -> (Sexpr (Pair (TagRef (name1),other)) , (offset,"MAKE_LITERAL_PAIR( const_tbl +" ^ (string_of_int (find_offset (find_const_by_name name1 !tagged_expressions) const_tbl)) ^ " , const_tbl +" ^ (string_of_int (find_offset (Sexpr(other)) const_tbl)) ^ ")"  ))
  | (Sexpr (Pair (other, TagRef (name2))) , (offset, asm_string )) -> (Sexpr (Pair (other, TagRef (name2))) , (offset, "MAKE_LITERAL_PAIR( const_tbl +" ^ (string_of_int (find_offset (Sexpr(other)) const_tbl)) ^ " , const_tbl +" ^ (string_of_int (find_offset (find_const_by_name name2 !tagged_expressions) const_tbl)) ^ ")" ))
  | _ -> tuple) in
List.map update_tagref const_tbl;;




let rec make_tuples (sexpr_list: constant list) (offset : int) (const_tbl : (constant* (int * string)) list) : (constant* (int * string)) list =
match sexpr_list with
| [] -> const_tbl
| hd:: tl -> (match hd with 
              | Sexpr(Number(Int (integer)))-> make_tuples tl (offset + number_object_length) (const_tbl @ [hd, (offset, "MAKE_LITERAL_INT("^(string_of_int integer)^")" )])
              | Sexpr(Number(Float (float)))-> make_tuples tl (offset + number_object_length) (const_tbl @ [hd, (offset,"MAKE_LITERAL_FLOAT("^(string_of_float float)^")")])
              | Sexpr (Char (char)) -> make_tuples tl (offset + char_object_length) (const_tbl @ [hd, (offset, "MAKE_LITERAL_CHAR('"^(Char.escaped char)^"')")])
              | Sexpr (String (string)) -> make_tuples tl (offset + (String.length string) + string_object_length) (const_tbl @ [(hd, (offset, "MAKE_LITERAL_STRING "^(string_of_int (String.length string))^ ", \"" ^ string ^"\""))])
              | Sexpr (Symbol (name_str)) -> make_tuples tl (offset + symbol_object_length) (const_tbl @ [hd, (offset, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (find_offset (Sexpr(String(name_str))) const_tbl))^")")])
              | Sexpr(TagRef(tag_name)) -> make_tuples tl offset const_tbl
              | Sexpr(Pair(car, cdr)) -> make_tuples tl (offset + (pointer_length * 2)+1) (const_tbl @ [(hd, (offset, "MAKE_LITERAL_PAIR( const_tbl +" ^ (string_of_int (find_offset (Sexpr(car)) const_tbl)) ^ " , const_tbl +" ^ (string_of_int (find_offset (Sexpr(cdr)) const_tbl) ^ ")")))])
              | Sexpr(TaggedSexpr(name, value)) -> make_tuples tl offset const_tbl 
              | _ -> raise (X_this_shouldnt_happen_error "from tuple"))
;;

let rec find_offset_fvars v fvars =
match fvars with
| [] -> raise X_this_should_not_happen
| hd::tl -> 
  (match hd with
  | (name, offset) -> if name = v then offset else (find_offset_fvars v tl)
  )
  ;;
(*| Bool of bool
  | Nil
  | Number of tuple
  | Char of char
  | String of string
  | Symbol of string
  | Pair of constant * constant
  | TaggedSexpr of string * constant
  | TagRef of string;;
*)
  let add_obligatory lst = 
  let obligatory = [(Sexpr Nil, (0,"MAKE_NIL")); (Void, (1,"MAKE_VOID")); (Sexpr (Bool true), (2 ,"MAKE_BOOL(1)")) ; (Sexpr (Bool false), (4 ,"MAKE_BOOL(0)"))] in
  obligatory@lst;;

  let make_list_for_consts_tbl asts =
  (replace_tagref (make_tuples (make_constant_lists asts) 6 (add_obligatory [])));;
(*
  let rec generate_asm consts fvars e = 
  match e with
  (*| Const'(Sexpr(Pair (car, cdr))) -> (Printf.sprintf "mov rax, (const_tbl+ %d)" (find_offset (Sexpr(Pair (car, cdr))) consts)) (* foramtted string *)
  | Const'(constant) -> (Printf.sprintf "lea rax, [const_tbl + %d]" (find_offset constant consts)) (* foramtted string *)
  *)
  | Const'(constant) -> (Printf.sprintf "lea rax, [const_tbl+ %d]" (find_offset constant consts))
  | Var'(VarFree (v)) -> (Printf.sprintf "mov rax, qword [fvar_tbl + %d * WORD_SIZE]" (find_offset_fvars v fvars))
  | Def' (Var'(VarFree (v)) , expr') -> (generate_asm consts fvars expr');
                                        (Printf.sprintf "\n mov [fvar_tbl + %d * WORD_SIZE], rax" (find_offset_fvars v fvars)) 
  | _ -> raise X_not_yet_implemented 
  ;;
*)
  let rec add_to_or generated_list list_to_return =
  match generated_list with
  | []-> list_to_return
  | hd::tl -> (match tl with
                | [] -> (add_to_or tl (list_to_return@[hd^"\n Lexit: "]))
                | _ -> (add_to_or tl (list_to_return@[hd^"\n cmp rax, SOB_FALSE_ADDRESS \n jne Lexit\n"]))
                );;

  let rec generate_asm consts fvars e = 
  match e with
  | Const'(constant) -> "lea rax, [const_tbl+ "^(string_of_int (find_offset constant consts)) ^"]" 
  | Var'(VarFree (v)) -> "mov rax, qword [fvar_tbl + "^(string_of_int (find_offset_fvars v fvars))^" * WORD_SIZE]" 
  | Def' (Var'(VarFree (v)) , expr') -> (generate_asm consts fvars expr')^"\n mov [fvar_tbl + "^(string_of_int (find_offset_fvars v fvars))^" * WORD_SIZE], rax \n lea rax, [const_tbl+1] \n" 
  | Seq' (expr'_list) -> (List.fold_left (fun  acc_string expr'-> acc_string^ (generate_asm consts fvars expr')^"\n")  "" expr'_list )
  | Or' (expr'_list) -> (let generated = List.map (fun expr' -> (generate_asm consts fvars expr')) expr'_list in
                          let generated = add_to_or generated [] in
                          List.fold_left (fun acc str -> acc^str) "" generated)
  
  | _ -> raise X_not_yet_implemented 
  ;;

  let make_consts_tbl asts = make_list_for_consts_tbl asts;;
  let make_fvars_tbl asts = primitive_vars@ (make_free_var_table asts);;
  let generate consts fvars e = generate_asm consts fvars e;;
  
end;;

