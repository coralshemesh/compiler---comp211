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
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let counter = ref 0;;
  (* val counter : int ref = {contents = 0} *)

  let next_val = 
      fun () ->
        counter := (!counter) + 1;
        !counter;;
  (* val next_val : unit -> int = <fun>  *)
(********************************create consts table*******************************)
let rec find_all_consts expr' lst = 
  match expr' with 
  | Const'(a) -> (List.append [a] lst )
  | Var'(a) -> lst
  | Box'(a) -> lst
  | BoxGet'(a) -> lst
  | BoxSet'(a,expr)-> find_all_consts expr lst
  | Or'(l) -> List.flatten (List.map (fun x ->  find_all_consts x lst)  l)
  | If'(test, thn, els) -> List.flatten [(find_all_consts test lst ); (find_all_consts thn lst);  (find_all_consts els lst )]   
  | Def'(vr , vl) -> find_all_consts vl lst
  | Set'(var, expr) -> find_all_consts expr lst
  | Applic'(rator, rands)-> List.append  (find_all_consts rator lst) (List.flatten (List.map (fun x ->  find_all_consts x lst)  rands))
  | ApplicTP' (rator, rands) -> List.append  (find_all_consts rator lst) (List.flatten (List.map (fun x ->  find_all_consts x lst)  rands))
  | LambdaSimple'(args, body) ->   find_all_consts body lst
  | LambdaOpt'( args , arg , body) -> find_all_consts body lst
  | Seq' (l) -> List.flatten (List.map (fun x ->  find_all_consts x lst)  l)

let rec convert_to_set lst new_lst=
  match lst with
  |[] -> new_lst 
  | hd::tl -> if (List.mem hd new_lst) = true 
            then (convert_to_set tl new_lst) 
            else (convert_to_set tl (List.append  new_lst [hd]))

let rec expand_to_sub_consts lst new_lst=
  match lst with
  |[] -> List.append new_lst lst
  |hd::tl -> (match hd with
              |Sexpr(Symbol a)-> expand_to_sub_consts tl (List.concat [[Sexpr(String a)]; [hd]; new_lst])
              |Sexpr(Pair(car,cdr)) -> expand_to_sub_consts tl (List.concat [(expand_to_sub_consts [(Sexpr car)] new_lst); (expand_to_sub_consts [(Sexpr cdr)] new_lst); [hd]; new_lst])
              |_-> expand_to_sub_consts tl (List.append [hd] new_lst))

let rec create_three_tuple_for_const lst addr const_tbl =
  match lst with
    | [] -> const_tbl
    | hd::tl->  (match hd with 
                    | Sexpr(String(a))-> let ascii_lst =(create_string_ascii (make_char_list a (String.length a) [] 0)) in create_three_tuple_for_const tl (addr+(String.length a)+9) (const_tbl@[(hd,(addr,Printf.sprintf ("db T_STRING, \n dq %d, \n db %s \n") (String.length a) ascii_lst))])
                    | Sexpr(Symbol(a))-> create_three_tuple_for_const tl (addr+9) (const_tbl@[(hd,(addr,"MAKE_LITERAL_SYMBOL(const_tbl+"^(get_sexpr_offset const_tbl (Sexpr (String a)))^")"))])
                    | Sexpr(Number(Fraction(num, d)))-> create_three_tuple_for_const tl (addr+17) (const_tbl@[(hd,(addr,"MAKE_LITERAL_RATIONAL("^(string_of_int num)^", "^(string_of_int d)^")"))])
                    | Sexpr(Number(Float(num)))-> create_three_tuple_for_const tl (addr+9) (const_tbl@[(hd,(addr,"MAKE_LITERAL T_FLOAT, dq "^(string_of_float num)))])
                    | Sexpr(Char(a))-> create_three_tuple_for_const tl (addr+2) (const_tbl@[(hd,(addr,"MAKE_LITERAL_CHAR("^(string_of_int (int_of_char a))^")"))])
                    | Sexpr(Pair(car, cdr))-> create_three_tuple_for_const tl (addr+17) (const_tbl@[(hd,(addr,"MAKE_LITERAL_PAIR(const_tbl+"^(get_sexpr_offset const_tbl (Sexpr car))^", const_tbl + "^(get_sexpr_offset const_tbl (Sexpr cdr))^") "))])
                    | _ -> create_three_tuple_for_const tl addr const_tbl)

and make_char_list str str_len lst index=
  if str_len =0 then lst
  else make_char_list str (str_len-1) (List. append lst  [Char.code (String.get str index)]) (index+1)

and create_string_ascii lst =
  match lst with
  | [] -> ""
  | hd :: [] -> (string_of_int hd)
  | hd :: tl  -> (string_of_int hd) ^ "," ^ (create_string_ascii tl)

and get_sexpr_offset const_tbl sexpr =
  match const_tbl with 
  |[]-> "0"
  |_ -> (string_of_int (fst (List.assoc sexpr const_tbl)))

(********************************create fvar table*******************************)
let rec find_all_fvars expr' lst = 
  match expr' with 
  | Const'(a) -> lst
  | Var'(a) -> (match a with
                |VarFree(name) -> List.append [name] lst
                | _-> lst)
  | Box'(a) -> find_all_fvars (Var' a) lst
  | BoxGet'(a) -> find_all_fvars (Var' a) lst
  | BoxSet'(a,expr)-> List.flatten [(find_all_fvars (Var' a) lst); (find_all_fvars expr lst)]
  | Or'(l) -> List.flatten (List.map (fun x ->  find_all_fvars x lst)  l)
  | If'(test, thn, els) -> List.flatten [(find_all_fvars test lst ); (find_all_fvars thn lst);  (find_all_fvars els lst )]   
  | Def'(vr , vl) -> List.flatten [(find_all_fvars (Var' vr) lst); (find_all_fvars vl lst)]
  | Set'(var, expr) -> List.flatten [(find_all_fvars (Var' var) lst); (find_all_fvars expr lst)]
  | Applic'(rator, rands)-> List.append  (find_all_fvars rator lst) (List.flatten (List.map (fun x ->  find_all_fvars x lst)  rands))
  | ApplicTP' (rator, rands) -> List.append  (find_all_fvars rator lst) (List.flatten (List.map (fun x ->  find_all_fvars x lst)  rands))
  | LambdaSimple'(args, body) ->   find_all_fvars body lst
  | LambdaOpt'( args , arg , body) -> find_all_fvars body lst
  | Seq' (l) -> List.flatten (List.map (fun x ->  find_all_fvars x lst)  l)

let rec make_indexed_string fvar_lst new_lst index=
  match fvar_lst with
  |[]-> new_lst
  | hd::tl -> (make_indexed_string tl (new_lst@[(hd,index*8)]) (index+1))


(********************************code generator*******************************)
let rec gen const_tbl fvar_tbl e env_size= 
  match e with 
  | Const'(a) -> "mov rax, const_tbl+"^(get_const_addr a const_tbl)^"\n"
  | Var'(VarFree(name)) -> let address = get_fvar_address name fvar_tbl in "mov rax, qword[fvar_tbl+"^ address^"]\n"
  | Var'(VarParam(_, minor)) -> "mov rax, qword[rbp+ 8*(4+" ^(string_of_int minor)^ ")] \n"
  | Var'(VarBound(_, major, minor)) -> "mov rax, qword[rbp + 8*2]\n 
                                        mov rax, qword[rax+ 8*"^(string_of_int major)^"]\n 
                                        mov rax, qword[rax+ 8*"^(string_of_int minor)^"] \n"
  | Set'(VarParam(_, minor),exp) -> (gen const_tbl fvar_tbl exp env_size)^"mov qword[rbp+ 8*(4+"^(string_of_int minor)^")], rax\n
                                        mov rax, SOB_VOID_ADDRESS\n"
  | Set'(VarBound(_, major, minor), exp) -> (gen const_tbl fvar_tbl exp env_size)^ "mov rbx, qword[rbp + 8*2] \n
                                              mov rbx, qword[rbx+ 8*"^(string_of_int major)^"] \n
                                              mov qword[rbx+ 8*"^(string_of_int minor)^"], rax \n
                                              mov rax, SOB_VOID_ADDRESS \n" 
  | Set'(VarFree(name), exp) -> let address = get_fvar_address name fvar_tbl in 
                                              (gen const_tbl fvar_tbl exp env_size)^"mov qword[fvar_tbl+"^address^"] ,rax \n
                                                                            mov rax , SOB_VOID_ADDRESS \n"  
  | Box'(VarParam(name, minor)) ->"MALLOC rax,8 \n  mov r8, qword [rbp+(4+"^(string_of_int minor)^")*WORD_SIZE] \n mov qword[rax], r8\n"                                            ^ " \n"
  | BoxGet'(a) -> (gen const_tbl fvar_tbl (Var' a) env_size)^"mov rax, qword[rax]\n"
  | BoxSet'(a,expr)-> (gen const_tbl fvar_tbl expr env_size)^"\n push rax \n"^(gen const_tbl fvar_tbl (Var' a) env_size)^ 
                      "\n pop qword[rax]\n mov rax, SOB_VOID_ADDRESS\n"
  | Or'(l) -> let index =next_val() in make_str_for_or l const_tbl fvar_tbl env_size "" index
  | If'(test, thn, els) ->let index =next_val() in  make_str_from_if test thn els const_tbl fvar_tbl env_size "" index 
  | Def'(VarFree(name), exp) -> let address = get_fvar_address name fvar_tbl in 
                    (gen const_tbl fvar_tbl exp env_size)^"mov qword[fvar_tbl+"^address^"] ,rax \n
                                                  mov rax , SOB_VOID_ADDRESS \n"
  | Applic'(rator, rands)-> let applic_str = make_str_for_applic rator (List.rev rands) const_tbl fvar_tbl env_size "push SOB_NIL_ADDRESS\n" (List.length rands) in
                            let index =next_val() in gen_applic applic_str index 0
  | ApplicTP' (rator, rands) -> let applic_str = make_str_for_applic rator (List.rev rands) const_tbl fvar_tbl env_size "push SOB_NIL_ADDRESS\n" (List.length rands) in
                                let index =next_val() in gen_applic applic_str index 1
  | LambdaSimple'(args, body) ->   make_str_from_lambdaSimple const_tbl fvar_tbl args body (env_size) 0 0
  (* | LambdaSimple'(args, body) ->   "" *)
  | LambdaOpt'( args , arg , body) -> make_str_from_lambdaSimple const_tbl fvar_tbl (args @ [arg]) body (env_size) (List.length args) 1
  | Seq'(l) -> concat_str (List.map (fun x -> (gen const_tbl fvar_tbl x env_size))  l) ""
  |_-> raise X_syntax_error



and make_str_from_if test thn els const_tbl fvar_tbl env_size str index = 
    str^"\n"^(gen const_tbl fvar_tbl test env_size)^"\n
    cmp rax, SOB_FALSE_ADDRESS
    je Lelse_"^(string_of_int index)^"\n"
    ^(gen const_tbl fvar_tbl thn env_size)^"\n
    jmp Lexit_"^(string_of_int index)^"\n
    Lelse_"^(string_of_int index)^":\n"
    ^(gen const_tbl fvar_tbl els env_size)^"\n
    Lexit_"^(string_of_int index)^":\n"

and make_str_for_applic rator rands const_tbl fvar_tbl env_size str num_of_args=
  match rands with
  |[] -> str^"\n"^"push "^(string_of_int num_of_args)^"\n"^(gen const_tbl fvar_tbl rator env_size)^"\n"
  |hd::tl -> let new_str = str^"\n"^(gen const_tbl fvar_tbl hd env_size)^"\n push rax\n" in
              make_str_for_applic rator tl const_tbl fvar_tbl env_size new_str num_of_args

and gen_applic applic_str index tp_flag=
let str_index = (string_of_int index) in
  let verify_closure = 
    "
    mov sil , byte[rax]
    cmp sil, T_CLOSURE
    je contiue_applic_"^str_index^
    
    "\nsend_error_closure_"^str_index^":\n
      jmp clean_exit_"^str_index^"\n

      contiue_applic_"^str_index^":\n
        CLOSURE_ENV r9, rax
        push r9
        CLOSURE_CODE r9, rax
        call r9
      
      add rsp, 8*1      ;pop env

      clean_exit_"^str_index^":\n
        pop rbx           ;get num of args
        shl rbx, 3
        add rbx, 8                       ;magic
        add rsp, rbx                 ;pop env, num of args, and all args\n" in 

    let verify_tp =
      "
      mov sil , byte[rax]
      cmp sil, T_CLOSURE
      je contiue_applic_"^str_index^"\n
      
      send_error_closure_"^str_index^":\n
        jmp exit_"^str_index^"\n
        
      contiue_applic_"^str_index^":\n
      CLOSURE_ENV r9, rax
      push r9

      ;when we call h from g, we do mov rbp, rsp, which means that when we jump to h rbp will be
      ;the old rsp which means it will point to g frame, and now after the call rsp changes to point 
      ;to h frame.

      mov r11, qword[rbp]        ;save old rbp. rbp points to 'rbp in f' on g stack

      push qword[rbp+8*1]        ;old ret address
      push r11

      mov r9,rbp
      sub r9, 8                     ;r9 now points to last element in h frame

      mov r8, qword[rbp+8*3]        ; get num of args for g function 
      add r8, 4                     ; add rbp in f, ret to f, lex env f, num of args f 
      shl r8, 3
      add r8, rbp                    ; r8 points to last element in g stack 

      loop_overwrite_stack_"^str_index^":\n
        mov r10, qword[r9]
        mov qword[r8], r10

        cmp r9, rsp
        jz finish_overwrite_stack_"^str_index^"\n

        sub r8 , 8 
        sub r9 , 8 
        jmp loop_overwrite_stack_"^str_index^"\n
      
      finish_overwrite_stack_"^str_index^":\n 
        mov rsp , r8             ;insert new rsp to rsp
       pop rbp           

      CLOSURE_CODE r9, rax
      jmp r9

      exit_"^str_index^":       ;clean stack as shown in class\n
      " in

    if tp_flag = 0 then  applic_str^"\n"^verify_closure else applic_str^"\n"^verify_tp
    
and make_str_for_or or_lst const_tbl fvar_tbl env_size str index =
  match or_lst with
  |[a] ->str^"\n"^(gen const_tbl fvar_tbl a env_size)^"Lexit_"^(string_of_int index)^":\n"
  |hd::tl -> let new_str = str^(gen const_tbl fvar_tbl hd env_size)^"cmp rax, SOB_FALSE_ADDRESS \n jne Lexit_"^(string_of_int index)^"\n" in
              make_str_for_or tl const_tbl fvar_tbl env_size new_str index
  | never -> raise X_syntax_error

and concat_str lst str=
  match lst with
  |[]->str
  |hd::tl -> concat_str tl (str^"\n"^hd)

and first_lambda const_tbl fvar_tbl args body env_size index opt_flag args_size= 
let str_index = (string_of_int index) in
if opt_flag=0 then
        " mov r15, SOB_NIL_ADDRESS
          MAKE_CLOSURE(rax, r15, Lcode_"^str_index^")\n
          jmp Lcont_"^str_index^"\n
          Lcode_"^str_index^":\n
          push rbp
          mov rbp, rsp 
          " ^(gen const_tbl fvar_tbl body (env_size+1) )^"\n
          leave
          ret\n
          Lcont_"^str_index^":\n"
      else 
      "
        mov r15, SOB_NIL_ADDRESS
        MAKE_CLOSURE(rax, r15, Lcode_"^str_index^")\n
        jmp Lcont_"^str_index^"\n

      Lcode_"^str_index ^ ":\n
      mov r8, qword[rsp+8*2]                         ;r8=n
      mov r9, "^(string_of_int args_size)^"\n  
      mov r10, r8
      sub r10, r9
      mov rcx, r10                                   ;save in rcx num of args in magic, loop counter \n
      inc r9

      cmp r8, r9
      jl no_adjust_needed"^str_index^" \n

      add r8, 2
      shl r8, 3
      add r8, rsp  

      mov r15, r8                                  ;save last arg pointer for adjust the stack\n
      mov r11, qword[r8]                           ;r8 now points to the last arg on stack\n

      MAKE_PAIR(rax, r11, SOB_NIL_ADDRESS)         ;make first pair fo magic list\n
      dec rcx

      cmp rcx, 0
      je finish_create_magic_loop_"^str_index^"\n

      create_magic_loop_"^str_index^":\n
        sub r8, 8
        mov r11, qword[r8]
        mov r12, rax
        MAKE_PAIR(rax, r11, r12)
      loop create_magic_loop_"^str_index^"\n

      finish_create_magic_loop_"^str_index^":\n
      mov qword[r15], rax                             ;insert all pairs in magics place
      sub r15,8                                       ;r15 points one before the last place
      sub r8,8                                        ;r8 now points to the first arg not included in magic              

      adjust_the_stack_"^str_index^":\n
        mov r10, qword[r8]
        mov qword[r15], r10

        cmp r8, rsp
        je change_rsp_"^str_index^"\n

        sub r15,8                                       ;points one before the last place
        sub r8,8 
      jmp adjust_the_stack_"^str_index^"\n

      change_rsp_"^str_index^":\n
        mov rsp, r15  
        mov r8, "^(string_of_int args_size)^"\n
        inc r8
        mov qword[rsp+8*2], r8

      no_adjust_needed"^str_index^":\n
        push rbp
        mov rbp, rsp \n" ^(gen const_tbl fvar_tbl body (env_size+1))^"\n
        leave
        ret\n 

        Lcont_"^str_index^":\n"

          

and make_str_from_lambdaSimple const_tbl fvar_tbl args body env_size args_size opt_flag=
  let index = next_val() in
  if env_size = 0 then (first_lambda const_tbl fvar_tbl args body env_size index opt_flag args_size) else
  let gen_body = (gen const_tbl fvar_tbl body (env_size+1)) in
  let str_index = (string_of_int index) in
  let new_env_part_1 = 
"  
    MALLOC rax,"^(string_of_int (env_size))^"*8
    mov r15, rax             ;save pointer to ExtEnv[0] for later\n

    mov rcx," ^(string_of_int env_size)^ "  ;loop counter\n
     cmp rcx, 1                               ; first env\n
     je copy_args_from_stack_"^str_index^"\n

     mov r8, rax            ;save pointer to ExtEnv[0]\n
     add r8 , 8             ; now r8 has the address of ExtEnv[1]\n
     mov r9, qword[rbp+8*2]  ;save current env, r9 points to CurrEnv[0]\n

    copy_curr_env_"^str_index^":    ;copy curr env\n
      mov r10, qword[r9] \n
      mov qword[r8], r10 \n
      add r8, 8
      add r9, 8
      loop copy_curr_env_"^str_index^"\n" in

    let new_env_part_2_simple =
    "copy_args_from_stack_"^str_index^":\n
      mov r10, qword[rbp+8*3]           ;get num of args
      ;cmp r10 , 0                       ;if no args
      ;jne regular_malloc_"^str_index^" \n

      inc r10           ;if no args so malloc 1 place for SOB NIL else malloc num of args

      regular_malloc_"^str_index^": \n                         
      imul r10, r10, 8                  
      MALLOC rax, r10                   ;malloc the args vector of curr lambda
      mov qword[r15], rax                ;save the new arg vector in ExtEnv[0]

      mov rcx, qword[rbp+8*3]           ;get num of args
      inc rcx
      cmp rcx, 0
      je no_args_"^str_index^"     ;if rcx is zero so args vector stays NIL\n

      mov r8, rbp
      add r8 , 8*4                              ;now r8 points to the first arg on stack\n
      mov r9, qword[r15]

      copy_args_"^str_index^": \n
        mov r10, qword[r8]                    ;ExtEnv[0] points to the new arg vector
        mov qword[r9], r10
        add r8, 8
        add r9, 8
        loop copy_args_"^str_index^"\n

      jmp end_copy_args_from_stack_"^str_index^"\n

      no_args_"^str_index^": \n
        mov r9, qword[r15]
        mov qword[r9], SOB_NIL_ADDRESS
        mov rax , 0

    end_copy_args_from_stack_"^str_index^":\n" in

      let new_env_part_2_opt = 
        "copy_args_from_stack_"^str_index^":\n
        mov r10, qword[rbp+8*3]           ;get num of args
        inc r10           ;if no args so malloc 1 place for SOB NIL else malloc num of args

        imul r10, r10, 8                  
        MALLOC rax, r10                   ;malloc the args vector of curr lambda
        mov qword[r15], rax                ;save the new arg vector in ExtEnv[0]
  
        mov rcx, qword[rbp+8*3]           ;get num of args
        inc rcx                           ;to copy the magic
        cmp rcx, 0
        je no_args_"^str_index^"     ;if rcx is zero so args vector stays NIL\n
  
        mov r8, rbp
        add r8 , 8*4                              ;now r8 points to the first arg on stack\n
        mov r9, qword[r15]
  
        copy_args_"^str_index^": \n
          mov r10, qword[r8]                    ;ExtEnv[0] points to the new arg vector
          mov qword[r9], r10
          add r8, 8
          add r9, 8
          loop copy_args_"^str_index^"\n
  
        jmp end_copy_args_from_stack_"^str_index^"\n
  
        no_args_"^str_index^": \n
          mov r9, qword[r15]
          mov qword[r9], SOB_NIL_ADDRESS
          mov rax , 0
  
      end_copy_args_from_stack_"^str_index^":\n
  " in

  let lcode_simple =
    " Lcode_"^str_index^":\n
    push rbp
    mov rbp, rsp \n" ^gen_body^"\n
    leave
    ret\n" in

  let lcode_opt = 
    "Lcode_"^str_index ^ ":\n
      mov r8, qword[rsp+8*2]                         ;r8=n
      mov r9, "^(string_of_int args_size)^"\n  
      mov r10, r8
      sub r10, r9
      mov rcx, r10                                   ;save in rcx num of args in magic, loop counter \n
      inc r9

      cmp r8, r9
      jl no_adjust_needed"^str_index^" \n

      add r8, 2
      shl r8, 3
      add r8, rsp  

      mov r15, r8                                  ;save last arg pointer for adjust the stack\n
      mov r11, qword[r8]                           ;r8 now points to the last arg on stack\n

      MAKE_PAIR(rax, r11, SOB_NIL_ADDRESS)         ;make first pair fo magic list\n
      dec rcx
      
      cmp rcx, 0
      je finish_create_magic_loop_"^str_index^"\n

      create_magic_loop_"^str_index^":\n
        sub r8, 8
        mov r11, qword[r8]
        mov r12, rax
        MAKE_PAIR(rax, r11, r12)
      loop create_magic_loop_"^str_index^"\n

      finish_create_magic_loop_"^str_index^":\n

      mov qword[r15], rax                             ;insert all pairs in magics place
      sub r15,8                                       ;r15 points one before the last place
      sub r8,8                                        ;r8 now points to the first arg not included in magic              

      adjust_the_stack_"^str_index^":\n
        mov r10, qword[r8]
        mov qword[r15], r10

        cmp r8, rsp
        je change_rsp_"^str_index^"\n

        sub r15,8                                       ;points one before the last place
        sub r8,8 
      jmp adjust_the_stack_"^str_index^"\n

      change_rsp_"^str_index^":\n
        mov rsp, r15  
        mov r8, "^(string_of_int args_size)^"\n
        inc r8
        mov qword[rsp+8*2], r8

      no_adjust_needed"^str_index^":\n
        push rbp
        mov rbp, rsp \n" ^gen_body^"\n
        leave
        ret\n "   in

  let gen_lambda_simple =
    if opt_flag=0 then 
    new_env_part_1^new_env_part_2_simple ^ "MAKE_CLOSURE (rax, r15, Lcode_"^str_index^") \n
    jmp Lcont_"^str_index^"\n
    "^lcode_simple ^ "Lcont_"^str_index^":"
    else 
    new_env_part_1^ new_env_part_2_opt ^ "MAKE_CLOSURE (rax, r15, Lcode_"^str_index^") \n
    jmp Lcont_"^str_index^"\n
    "^lcode_opt ^ "Lcont_"^str_index^":"
  in gen_lambda_simple

and get_fvar_address name fvar_tbl = 
(string_of_int (List.assoc name fvar_tbl))

and get_const_addr sexpr const_tbl =
  (string_of_int (fst (List.assoc sexpr const_tbl)))

(***************************************module functions*************************************)
let make_consts_tbl asts = 
  let first_const_set = convert_to_set (List.flatten (List.map (fun x -> find_all_consts x []) asts)) [] in
  let expanded_tbl = expand_to_sub_consts first_const_set [] in
  let expanded_set = convert_to_set expanded_tbl [] in
  let final_tbl = create_three_tuple_for_const expanded_set 6 [(Void, (0, "MAKE_VOID"));
                                            (Sexpr(Nil), (1, "MAKE_NIL"));
                                            (Sexpr(Bool false), (2, "MAKE_BOOL(0)"));
                                            (Sexpr(Bool true), (4, "MAKE_BOOL(1)"));] in
  final_tbl;;

let make_fvars_tbl asts =
  let fvar_set = convert_to_set (List.flatten (List.map (fun x -> find_all_fvars x ["boolean?";"flonum?" ; "rational?";
  "pair?"; "null?" ; "char?";
  "string?"; "procedure?";
  "symbol?"; "string-length";
  "string-ref";  "string-set!";
  "make-string"; "symbol->string";
  "char->integer"; "integer->char"; 
  "exact->inexact"; "eq?"; "+";
  "*"; "/"; "="; "<";
  "numerator"; "denominator"; "gcd"; "car"; "cdr";  "set-car!"; "set-cdr!"; "apply";"cons"
  ]) asts)) [] in

  let final_tbl = make_indexed_string fvar_set [] 0 in 
  final_tbl;;


let generate consts fvars e = 
  gen consts fvars e 0;;
                                      
  end;;
