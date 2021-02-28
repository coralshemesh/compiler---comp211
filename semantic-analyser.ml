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
  | Set' of var * expr'
  | Def' of var * expr'
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
  | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
  | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
  | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
  | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
  | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
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


(********************************3.2*******************************)
let rec lexical_addresses e env_list =
  match e with
  | Const(a) -> Const' (a)
  | Var(a) -> Var'(check_var a env_list 0)
  | If (test,thn,els) -> If' ((lexical_addresses test env_list), (lexical_addresses thn env_list), (lexical_addresses els env_list))
  | Seq (lst) -> Seq' (List.map (fun x -> (lexical_addresses x env_list)) lst )
  | Set (var , expr) -> (set_handler var expr env_list)
  | Def (var , valu) -> def_check_var (lexical_addresses var env_list) (lexical_addresses valu env_list)
  | Or (lst) -> Or' (List.map (fun x -> (lexical_addresses x env_list)) lst )
  | LambdaSimple(args, body) -> (lambda_simple_handler args body env_list)
  | LambdaOpt (args, arg, body) -> (lambda_opt_handler args arg body env_list)
  | Applic(op , rands) -> Applic' ((lexical_addresses op env_list), (List.map (fun x -> (lexical_addresses x env_list)) rands ))

  and set_handler var expr env_list =
    match var with
    | Var(a) -> Set' ( (check_var a env_list 0), (lexical_addresses expr env_list))
    | _ -> raise X_syntax_error

  and lambda_opt_handler args arg body env =
    let all_args = List.append args [arg] in
    let new_env = add_vars_to_env all_args env in
    LambdaOpt' (args, arg , (lexical_addresses body new_env))

  and lambda_simple_handler args body env =
    let new_env = add_vars_to_env args env in
    LambdaSimple' (args, (lexical_addresses body new_env))

  and add_vars_to_env vr_lst env =
    List.cons vr_lst env

  and def_check_var vr vl=
    match vr with
    | Var'(VarFree(a)) -> Def'(VarFree(a), vl)
    |_-> raise X_syntax_error

  and check_var v env_list maj =
  match env_list with
  | [] -> (VarFree (v))
  | h::t -> let minor = (check_if_exist h v 0)  in
            if maj = 0 then
              (match minor with
                  | (-1) -> check_var v t (maj+1)
                  | _-> VarParam (v, minor))
            else
              (match minor with
              | (-1) -> check_var v t (maj+1)
              | _-> VarBound (v, (maj-1), minor))

  and  check_if_exist lst v min=
    match lst with
    | [] -> (-1)
    | _ -> if (List.hd lst) = v then min else check_if_exist (List.tl lst) v (min + 1)

let annotate_lexical_addresses e =
  lexical_addresses e [[]] ;;

(********************************3.3*******************************)
let rec remove_at n = function
  | [] -> []
  | h :: t -> if n = 0 then t else h :: remove_at (n-1) t;;

let rec tail_position e tp =
  match e with
  | Const'(a) -> e
  | Var'(a) -> e
  | Or'(lst) ->  Or' (or_tail_position lst tp)
  | If'(test, thn, els) -> (if_tail_position test thn els tp)
  | Def'(vr , vl) -> Def' (vr , (tail_position vl false))
  | LambdaSimple'(args, body) -> LambdaSimple'( args, (tail_position body true))
  | LambdaOpt'( args , arg , body) -> LambdaOpt'(args, arg, tail_position body true)
  | Applic'(rator, rands)-> (applic_tail_position rator rands tp)
  | Seq' (lst) -> Seq' (or_tail_position lst tp)
  | Set'(var, expr) -> Set'(var, (tail_position expr false))
  |_->raise X_syntax_error

and applic_tail_position rator rands tp =
  match tp with
  | true -> ApplicTP'((tail_position rator false) , (List.map (fun x -> (tail_position x false)) rands))
  | false -> Applic'((tail_position rator false) , (List.map (fun x -> (tail_position x false)) rands))

and if_tail_position test thn els tp =
  If' ((tail_position test false ),(tail_position thn tp), (tail_position els tp))

and or_tail_position lst tp =
  let len = List.length lst in
  let last_exp = List.nth lst (len-1) in
  let new_last_exp = (tail_position last_exp tp) in
  let fun1 = remove_at (len -1) in
  let lst_without_last = fun1 lst in
  let or_elements = (List.map (fun x -> (tail_position x false)) lst_without_last) in
  (List.append or_elements [new_last_exp])

let annotate_tail_calls e =
  tail_position e false;;

(********************************3.4*******************************)
let rec box e =
  match e with
  | Const'(a) -> e
  | Var'(a) -> e
  | Box'(a) -> e
  | BoxGet'(a) -> e
  | BoxSet'(a,expr)-> BoxSet'(a, box expr)
  | Or'(lst) ->  Or' (List.map box lst)
  | If'(test, thn, els) ->If'(box test, box thn, box els)
  | Def'(vr , vl) -> Def' (vr , box vl)
  | Set'(var, expr) -> Set' (var, box expr)
  | Applic'(rator, rands)-> Applic' (box rator, (List.map box rands))
  | ApplicTP' (rator, rands) -> ApplicTP' (box rator, List.map box rands)
  | LambdaSimple'(args, body) -> LambdaSimple'(args, lambda_simple_handler args body)
  | LambdaOpt'( args , arg , body) -> LambdaOpt'(args, arg, lambda_simple_handler (List.append args [arg]) body)
  | Seq' (lst) -> Seq' (List.map box lst)

and lambda_simple_handler args body =
  match args with
  | [] -> box body
  | _ -> (let which_arg_should_box = List.map (fun x-> ((check_all_conds x body (address_of body)))) args in
          let fresh_body = new_body which_arg_should_box body in
          let fresh_body_with_param = change_var_param_to_box (List.rev which_arg_should_box) fresh_body ((List.length which_arg_should_box)-1)  in
          box fresh_body_with_param)

(*returns true if we need to do boxing*)
and check_all_conds arg body address=
  let set_get_list = find_all_gets_and_sets arg body (-1) address in
  match body with
  | Seq'(lst)-> let first_and_second_cond = check_read_write_for_seq set_get_list  in
                (*let third_cond = check_third_cond arg lst in*)
                (arg, first_and_second_cond (*&& third_cond*) )
  | _ ->  let first_and_second_cond_rest = check_read_write_other_then_seq set_get_list body in
            (arg,first_and_second_cond_rest)

(************************************create new body functions*******************************************)
and change_var_param_to_box lst_pair fresh_body index=
  match lst_pair with
  |[] -> fresh_body
  |hd::tl -> (match hd with
            |(a,b)-> if b=true then (let fresh_param = Set'(VarParam(a,index), Box'(VarParam(a,index))) in
                                        match fresh_body with
                                        |Seq'(lst)-> change_var_param_to_box tl (Seq' (List.append [fresh_param] lst)) (index-1)
                                        |_-> change_var_param_to_box tl (Seq'(List.append [fresh_param] [fresh_body])) (index-1))
                        else change_var_param_to_box tl fresh_body (index-1))

and new_body lst_pairs body =
  match lst_pairs with
  | [] -> body
  | hd::tl -> (match hd with
              |(a,b)-> if b = true then let boxed_body =create_new_body_with_box a body (-1) in
                                        new_body tl boxed_body
                                    else new_body tl body)

and create_new_body_with_box arg expr counter=
  match expr with
    | Const'(a) -> expr
    | Var'(a) -> (match a with
                  | VarFree(x) -> expr
                  | VarBound(name, major, minor)-> if (counter = major && arg=name) then BoxGet'(a) else expr
                  | VarParam(name, minor)-> if (arg=name && counter =(-1)) then BoxGet'(a) else expr)
    | Box'(a) -> expr
    | BoxGet'(a) -> expr
    | BoxSet'(a,e)-> BoxSet' (a, create_new_body_with_box arg e counter)
    | Seq'(lst) -> Seq'(List.map (fun e -> create_new_body_with_box arg e counter ) lst)
    | Or'(lst) ->  Or'(List.map (fun e -> create_new_body_with_box arg e counter ) lst)
    | If'(test, thn, els) -> If'((create_new_body_with_box arg test counter), (create_new_body_with_box arg thn counter), (create_new_body_with_box arg els counter))
    | Def'(vr , vl) -> Def'(vr, (create_new_body_with_box arg vl counter))
    | Set'(var, e) -> (match var with
                          |VarFree(x) -> Set' (var, create_new_body_with_box arg e counter)
                          |VarBound(name,major,minor)-> if (name=arg && major=counter) then BoxSet'(var , create_new_body_with_box arg e counter) else (Set'(var, create_new_body_with_box arg e counter))
                          |VarParam(name, minor)-> if (arg=name && counter =(-1)) then BoxSet'(var,create_new_body_with_box arg e counter) else (Set' (var, create_new_body_with_box arg e counter)))
    | Applic'(rator, rands)-> Applic' ((create_new_body_with_box arg rator counter), (List.map (fun e -> create_new_body_with_box arg e counter) rands))
    | ApplicTP' (rator, rands) -> ApplicTP' ((create_new_body_with_box arg rator counter), (List.map (fun e -> create_new_body_with_box arg e counter) rands))
    | LambdaSimple'(args, body) -> LambdaSimple' (args,create_new_body_with_box arg body (counter+1))
    | LambdaOpt'( args , opt_arg , body) -> LambdaOpt' (args, opt_arg ,create_new_body_with_box arg body (counter+1))

(******************************************check third cond functions************************************************)
(* this function returns false if one of the conditions is true beacuse we don't need to box if one of the  conds is true *)
(* and check_third_cond arg expr_lst =
  match expr_lst with
  | [] -> true
  | hd::tl ->
     (match hd with
     |Var'(VarParam(name , minor))-> (if (check_if_write_occur (List.tl expr_lst) arg) = false then
                                      check_third_cond arg tl
                                      else false)
     |Set'(vr, vl)-> (if (check_if_read_occur (List.tl expr_lst) arg) = false then
                      check_third_cond arg tl
                      else false)
      | _ -> check_third_cond arg tl)

and check_if_read_occur expr_lst name =
  match expr_lst with
  |[] -> false
  |_-> let set_get = (make_get_set_list name (List.hd expr_lst) (-1) [] 0) in
        if (check_if_var_bound_not_set set_get) = true then true
        else check_if_read_occur (List.tl expr_lst) name

and check_if_write_occur expr_lst name =
  match expr_lst with
  | [] -> false
  | _ -> let set_get = (make_get_set_list name (List.hd expr_lst) (-1) [] 0) in
          if check_if_var_bound_in_set set_get = true then true
          else check_if_write_occur (List.tl expr_lst) name

and check_if_var_bound_not_set lst =
  match lst with
  | [] -> false
  | hd::tl -> (match hd with
              | (Var'(VarBound(name, major,minor)),b,c)-> true
              | _ -> check_if_var_bound_not_set tl)

and check_if_var_bound_in_set lst =
  match lst with
  | [] -> false
  | hd::tl -> (match hd with
              | (Set'(VarBound(name, major, minor),vl),b,c)-> true
              | _ -> check_if_var_bound_in_set tl) *)

(**********************help functions to check first and second cond*******************************)

(*check if read/write exists in a list*)
(*returns true if found one appearance*)
and check_read lst=
  match lst with
  | [] -> false
  | (Var'(a),b,c)::tl-> true
  | _-> check_read (List.tl lst)

and check_write lst=
    match lst with
    | [] -> false
    | (Set'(vr,vl),b,c)::tl-> true
    | _-> check_write (List.tl lst)

(*create a new list of all sets found in a list*)
and find_set lst set_lst=
  match lst with
  |[] -> set_lst
  |hd::tl -> (match hd with
              | (Set'(vr, vl),a,b)-> find_set tl (List.append [hd] set_lst)
              |_-> find_set tl set_lst)
  
(*create a new list of all gets found in a list*)
and find_get lst get_lst=
  match lst with
  |[] -> get_lst
  |hd::tl -> (match hd with
              |(Var'(a), b , c)-> find_get tl (List.append [hd] get_lst)
              |_-> find_get tl get_lst)

(*check if there are read and write not in the same rib*)
(*returns false if shouldnt box else returns true*)
and check_if_not_in_same_rib get_set_lst =
  match get_set_lst with
  |[] -> false
  |_-> check_ribs (List.hd get_set_lst)

and check_ribs set_get_lst =
  match set_get_lst with
    |[] -> false
    |hd::tl -> (match hd with
                |(Var'(a), b , c)-> let set_exp = find_set tl [] in
                            if set_exp = [] then false
                            else if (List.mem false (List.map (fun x -> c = (get_lambda_address x)) set_exp)) = false
                            then check_ribs tl
                            else true
                |(Set'(vr, vl), b,c) -> let get_exp = find_get tl [] in
                                      if get_exp = [] then false
                                      else if (List.mem false (List.map (fun x -> c = (get_lambda_address x)) get_exp)) = false
                                      then check_ribs tl
                                      else true
                |_->raise X_syntax_error)

(*check if there is a common ancestor for read and write we found*)
(*returns true if they have common ancestor*)
and find_common_ancestor get_set_lst body_lambda =
  match get_set_lst with
    |[]-> false
    |_ -> check_pairs (List.hd get_set_lst) body_lambda

(*for each pair of write and read check if they have common ancestor*)
and check_pairs get_set_lst body_lambda=
  match get_set_lst with
  |[] -> false
  |hd::tl -> (match hd with
              |(Var'(a), b , c)-> let set_exp = find_set tl [] in
                          if set_exp = [] then false
                          else if (List.mem true (List.map (fun x -> (have_ancestor body_lambda (get_address hd) (get_address x))) set_exp)) = true
                          then check_pairs tl body_lambda
                          else false
              |(Set'(vr, vl), b,c) -> let get_exp = find_get tl [] in
                              if get_exp = [] then false
                              else if (List.mem true (List.map (fun x -> (have_ancestor body_lambda (get_address hd) (get_address x))) get_exp)) = true
                              then check_pairs tl body_lambda
                              else false
              |_-> raise X_syntax_error)

(* return true if common ancestor exists by the pair addresss*)
and have_ancestor lambda_body first_addr second_addr=
  match lambda_body with
    | Const'(a)-> false
    | Var'(a)-> false
    | Box'(a)-> false
    | BoxGet'(a) -> false
    | Def'(vr,vl)->false
    | BoxSet'(a,e) -> have_ancestor e first_addr second_addr
    | Seq'(lst) -> List.mem true (List.map (fun x -> have_ancestor x first_addr second_addr) lst)
    | LambdaSimple'(args, body) -> (find_exp_addr_in_lambda body first_addr) && (find_exp_addr_in_lambda body second_addr)
    | LambdaOpt'(args,arg, body) ->(find_exp_addr_in_lambda body first_addr) && (find_exp_addr_in_lambda body second_addr)
    | If'(test, thn, els) -> (have_ancestor test first_addr second_addr)|| (have_ancestor thn first_addr second_addr) || (have_ancestor els first_addr second_addr)
    | Or'(lst) -> List.mem true (List.map (fun x -> have_ancestor x first_addr second_addr) lst)
    | Applic'(op, rands)-> (have_ancestor op first_addr second_addr)|| (List.mem true (List.map (fun x -> have_ancestor x first_addr second_addr) rands))
    | ApplicTP'(op, rands)-> (have_ancestor op first_addr second_addr)|| (List.mem true (List.map (fun x -> have_ancestor x first_addr second_addr) rands))
    | Set'(vr, vl) -> have_ancestor vl first_addr second_addr

(*returns true if found the expr address in the lambda body*)
and find_exp_addr_in_lambda body addr =
  match body with
  |Const'(a)-> false
  |Var'(a) -> (address_of body) = addr
  |Box'(a) -> false
  |BoxGet'(a) -> false
  |BoxSet'(a,e)-> false
  |Def'(vr,vl)->false
  |If'(test, thn, els) -> (find_exp_addr_in_lambda test addr)||(find_exp_addr_in_lambda thn addr)||(find_exp_addr_in_lambda els addr)
  |Seq'(lst) -> List.mem true (List.map (fun x -> find_exp_addr_in_lambda x addr) lst)
  |Set'(vr, vl) -> (address_of body) = addr
  |Or'(lst) -> List.mem true (List.map (fun x -> find_exp_addr_in_lambda x addr) lst)
  |LambdaSimple'(args, lam_body) -> find_exp_addr_in_lambda lam_body addr
  |LambdaOpt'(args,arg, lam_body) -> find_exp_addr_in_lambda lam_body addr
  |Applic'(op, rands) -> (find_exp_addr_in_lambda op addr)||(List.mem true (List.map (fun x -> find_exp_addr_in_lambda x addr) rands))
  |ApplicTP'(op, rands) -> (find_exp_addr_in_lambda op addr)||(List.mem true (List.map (fun x -> find_exp_addr_in_lambda x addr) rands))
  
and address_of e =
  (1* (Obj.magic e))

and get_address pair =
  match pair with
    |(a, b , c) -> b

and get_lambda_address pair =
  match pair with
    |(a, b , c) -> c

(*******************************check first and second cond*****************************************)
and check_read_write_for_seq set_get_list =
  match set_get_list with
  |[] -> false
  | _ ->
      (match (List.hd set_get_list) with
      |[] -> check_read_write_for_seq (List.tl set_get_list)
      |_ -> (let read_bool = (check_read (List.hd set_get_list)) in
            let write_bool = (check_write (List.hd set_get_list)) in
            let tail_have_read = (List.mem true (List.map  check_read (List.tl set_get_list))) in
            let tail_have_write = List.mem true (List.map check_write (List.tl set_get_list)) in
           if read_bool  = true
              then if tail_have_write =true
                      then true
                      else if write_bool = true
                            then  if tail_have_read = true
                                  then true
                                  else  (check_read_write_for_seq (List.tl set_get_list))
                            else  (check_read_write_for_seq (List.tl set_get_list))
            else
              if write_bool = true
              then if tail_have_read = true
                    then true
                    else  check_read_write_for_seq (List.tl set_get_list)
              else check_read_write_for_seq (List.tl set_get_list)))

and check_read_write_other_then_seq set_get_list body=
  (check_read (List.hd set_get_list)) && (check_write (List.hd set_get_list)) && (check_if_not_in_same_rib set_get_list) && (not(find_common_ancestor set_get_list body))

(*****************************create set ang get list functions**********************************)
and find_all_gets_and_sets arg lambda_body counter address=
  match lambda_body with
  | Seq'(lst) -> List.map (fun expr -> make_get_set_list arg expr counter [] address) lst
  | _-> [make_get_set_list arg lambda_body counter [] address]

and make_get_set_list arg expr counter get_set_lst address=
  match expr with
    | Const'(a) ->[]
    | Var'(a) -> (match a with
                  | VarFree(x) -> get_set_lst
                  | VarBound(name, major, minor)-> if (counter = major && arg=name) then (List.append [(expr,(address_of expr),address)] get_set_lst) else []
                  | VarParam(name, minor)-> if (arg=name && counter =(-1)) then (List.append [(expr,(address_of expr),address)] get_set_lst) else [])
    | Box'(a) -> []
    | BoxGet'(a) ->[]
    | BoxSet'(a,e)-> List.append (make_get_set_list arg e counter get_set_lst address) get_set_lst
    | Or'(lst) ->  List.concat [(List.flatten (List.map (fun e -> make_get_set_list arg e counter get_set_lst address) lst)); get_set_lst]
    | If'(test, thn, els) -> List.concat [(make_get_set_list arg test counter get_set_lst address); (make_get_set_list arg thn counter get_set_lst address); (make_get_set_list arg els counter get_set_lst address); get_set_lst]
    | Def'(vr , vl) ->List.concat [(make_get_set_list arg vl counter get_set_lst address); get_set_lst]
    | Set'(var, e) ->(match var with
                          |VarFree(x) -> List.append (make_get_set_list arg e counter get_set_lst address) get_set_lst
                          |VarBound(name,major,minor)-> if (name=arg && major = counter) then List.concat [[(expr,(address_of expr),address)]; (make_get_set_list arg e counter get_set_lst address); get_set_lst] else (List.append (make_get_set_list arg e counter get_set_lst address) get_set_lst)
                          |VarParam(name, minor)-> if (arg=name && counter =(-1)) then List.concat [[(expr,(address_of expr),address)]; (make_get_set_list arg e counter get_set_lst address); get_set_lst] else (List.append (make_get_set_list arg e counter get_set_lst address) get_set_lst))
    | Applic'(rator, rands)->  List.concat [(make_get_set_list arg rator counter get_set_lst address);  List.flatten(List.map (fun e -> make_get_set_list arg e counter get_set_lst address) rands); get_set_lst]
    | ApplicTP' (rator, rands) -> List.concat [(make_get_set_list arg rator counter get_set_lst address);  List.flatten(List.map (fun e -> make_get_set_list arg e counter get_set_lst address) rands); get_set_lst]
    | LambdaSimple'(args, body) ->List.append (List.flatten (find_all_gets_and_sets arg body (counter+1) (address_of expr))) get_set_lst
    | LambdaOpt'( args , opt_arg , body) -> List.append (List.flatten (find_all_gets_and_sets arg body (counter+1) (address_of expr))) get_set_lst
    | Seq'(lst) ->  List.flatten (List.map (fun expr -> make_get_set_list arg expr counter [] address) lst)

let box_set e = box e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
        (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)



(* 
and make_get_set_list arg expr counter get_set_lst address=
  match expr with
    | Const'(a) ->let print = Printf.printf "%s\n" "const" in []
    | Var'(a) ->let print = Printf.printf "%s\n" "var" in (match a with
                  | VarFree(x) -> get_set_lst
                  | VarBound(name, major, minor)-> if (counter = major && arg=name) then (List.append [(expr,(address_of expr),address)] get_set_lst) else []
                  | VarParam(name, minor)-> if (arg=name && counter =(-1)) then (List.append [(expr,(address_of expr),address)] get_set_lst) else [])
    | Box'(a) -> let print = Printf.printf "%s\n" "box" in []
    | BoxGet'(a) ->let print = Printf.printf "%s\n" "box get" in []
    | BoxSet'(a,e)->let print = Printf.printf "%s\n" "box set" in List.append (make_get_set_list arg e counter get_set_lst address) get_set_lst
    | Or'(lst) -> let print = Printf.printf "%s\n" "or" in List.concat [(List.flatten (List.map (fun e -> make_get_set_list arg e counter get_set_lst address) lst)); get_set_lst]
    | If'(test, thn, els) ->let print = Printf.printf "%s\n" "if" in List.concat [(make_get_set_list arg test counter get_set_lst address); (make_get_set_list arg thn counter get_set_lst address); (make_get_set_list arg els counter get_set_lst address); get_set_lst]
    | Def'(vr , vl) ->let print = Printf.printf "%s\n" "def" in List.concat [(make_get_set_list arg vl counter get_set_lst address); get_set_lst]
    | Set'(var, e) ->let print = Printf.printf "%s\n" "Set" in (match var with
                          |VarFree(x) -> List.append (make_get_set_list arg e counter get_set_lst address) get_set_lst
                          |VarBound(name,major,minor)-> if (name=arg && major = counter) then List.concat [[(expr,(address_of expr),address)]; (make_get_set_list arg e counter get_set_lst address); get_set_lst] else (List.append (make_get_set_list arg e counter get_set_lst address) get_set_lst)
                          |VarParam(name, minor)-> if (arg=name && counter =(-1)) then List.concat [[(expr,(address_of expr),address)]; (make_get_set_list arg e counter get_set_lst address); get_set_lst] else (List.append (make_get_set_list arg e counter get_set_lst address) get_set_lst))
    | Applic'(rator, rands)-> let print = Printf.printf "%s\n" "applic" in List.concat [(make_get_set_list arg rator counter get_set_lst address);  List.flatten(List.map (fun e -> make_get_set_list arg e counter get_set_lst address) rands); get_set_lst]
    | ApplicTP' (rator, rands) -> let print = Printf.printf "%s\n" "applicTP" in List.concat [(make_get_set_list arg rator counter get_set_lst address);  List.flatten(List.map (fun e -> make_get_set_list arg e counter get_set_lst address) rands); get_set_lst]
    | LambdaSimple'(args, body) ->let print = Printf.printf "%s\n" "lambda simple" in List.append (List.flatten (find_all_gets_and_sets arg body (counter+1) (address_of expr))) get_set_lst
    | LambdaOpt'( args , opt_arg , body) ->let print = Printf.printf "%s\n" "lambda opt" in List.append (List.flatten (find_all_gets_and_sets arg body (counter+1) (address_of expr))) get_set_lst
    | Seq'(lst) -> let print = Printf.printf "%s\n" "Seq" in List.flatten (List.map (fun expr -> make_get_set_list arg expr counter [] address) lst)
    | never -> raise X_syntax_error *)