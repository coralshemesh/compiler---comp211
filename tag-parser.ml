#use "reader.ml";;
#use "pc.ml";;
open PC;;
open Reader;;

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
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;

(* work on the tag parser starts here *)

(********************************help functions*******************************)
let check_if_valid word lst =
  List.mem word lst;;

let rec args_to_string_list args =
    match args with
    | Nil -> []
    | Pair (Symbol(x), y) ->  x::(args_to_string_list y)
    | never -> raise X_syntax_error;;

let rec args_without_the_last_one args =
  match args with
  | Pair (Symbol(x) , Pair(y, z)) -> x:: (args_without_the_last_one (Pair(y,z)))
  | Pair (Symbol (x), y)-> [x]
  | _-> raise X_syntax_error;;

let rec last_arg args =
  match args with
  |Pair (x , y) -> (last_arg y)
  |Symbol(y)-> y
  | never -> raise X_syntax_error;;

let rec is_proper_list lst =
  match lst with
  |Nil -> true
  |Pair (x , y) -> (is_proper_list y)
  |_ -> false;;

let length l =
  let rec f n = function
    | []-> n
    | _::t -> f (n+1) t
  in f 0 l;;

let rec flat_the_seq lst =
  if lst = [] then []
  else
        match (List.hd lst) with
        |Seq(a)-> flat_the_seq a
        | _-> List.append [(List.hd lst)] (flat_the_seq (List.tl lst))

(********************************main functions*******************************)
let rec tag_parser sexp =
  match sexp with
  | Nil -> Const(Void)
  | Bool(x) -> Const(Sexpr sexp)
  | Number(x)-> Const (Sexpr sexp)
  | Char(x)-> Const (Sexpr sexp)
  | String(x)-> Const (Sexpr sexp)
  | Symbol(x)-> if (check_if_valid x reserved_word_list) = true then raise X_syntax_error else Var(x)
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Pair (Symbol ("unquote"),Pair(x, Nil))-> (tag_parser x)
  | Pair (Symbol ("quasiquote"), Pair(x, Nil)) -> (tag_parser (tag_quasiquote x))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil))))->If(tag_parser test, tag_parser dit, tag_parser dif)
  | Pair(Symbol("if"), Pair (test, Pair (dit , Nil))) -> If (tag_parser test, tag_parser dit, Const(Void))
  | Pair(Symbol ("lambda"), Pair (args , body)) -> (tag_lambda (Pair (args , body)))
  | Pair (Symbol ("or"),lst)-> (match lst with |Nil -> Const(Sexpr(Bool false)) |Pair(a,Nil)-> (tag_parser a ) |_->Or (create_expr_list lst))
  | Pair (Symbol ("define"), rest)-> (tag_define rest)
  | Pair (Symbol ("set!"), rest) -> (tag_set rest)
  | Pair (Symbol ("begin"), rest) -> (match rest with |Pair(a,Nil)-> List.hd (flat_the_seq(tag_begin rest)) |_-> Seq(flat_the_seq(tag_begin rest)))
  | Pair(Symbol("cond"),ribs)-> (tag_parser (tag_cond ribs))
  | Pair(Symbol("let"), Pair(Nil, body))-> (tag_parser (tag_let_no_ribs body))
  | Pair (Symbol "let" , Pair(bindings , body)) -> (tag_parser (tag_let_with_ribs bindings body ))
  | Pair (Symbol ("let*"), Pair(args, body))-> tag_parser (tag_let_star args body)
  | Pair (Symbol ("and"), x) -> tag_parser (tag_and x)
  | Pair (Symbol ("letrec"), Pair(bindings, body)) -> tag_parser (tag_letrec bindings body)
  | Pair (Symbol ("pset!"),rest) -> tag_parser(tag_pset rest)
  | Pair (op, params) ->  Applic ((tag_parser op), (create_expr_list params))

  (********************************pset and set*******************************)
  and create_pairs vars vals =
    match vars, vals with
    | Nil, Nil -> Nil
    | Pair ( vr , vr_rest) , Pair(vl , vl_rest) -> Pair(Pair(vr , Pair (vl , Nil)), create_pairs vr_rest vl_rest)
    | never -> raise X_syntax_error

 and make_var_gen len n vars_list=
  match len with
  | 0 -> Nil
  | _ -> let string_num = string_of_int n in
          if (List.mem (Var("x"^string_num)) vars_list) then (make_var_gen len (n+1) vars_list)
          else Pair(Symbol ("x"^string_num), (make_var_gen (len-1) (n+1) (List.append vars_list [Var("x"^string_num)])))

  and tag_pset bindings =
  let all_vars = get_vars bindings in
  let all_vals = get_vals bindings in
  let vars_as_expr = create_expr_list all_vars in
  let len = length vars_as_expr in
  let new_vars = make_var_gen len 0 vars_as_expr in
  let bindings = create_pairs new_vars all_vals in
  let body_set = create_set_for_pset all_vars new_vars in
  Pair (Symbol "let", Pair(bindings, body_set))

  and create_set_for_pset vars vals =
  match vars, vals with
  | Nil, Nil -> Nil
  | Pair ( vr , vr_rest) , Pair(vl , vl_rest) -> Pair(Pair(Symbol "set!", Pair(vr ,Pair (vl, Nil))), create_set_for_pset vr_rest vl_rest )
  | never -> raise X_syntax_error

  and tag_set x =
  match x with
  | Pair(vr, vl) ->
        let my_var = (tag_parser vr) in
        (match my_var with
          | Var(_)-> Set( my_var, tag_body vl)
          |_-> raise X_syntax_error)
  |_-> raise X_syntax_error
(********************************letrec*******************************)

  and create_set_for_letrec vars vals body =
    match vars, vals with
    | Nil, Nil -> Pair(Pair(Symbol "let", Pair(Nil, body)),Nil)
    | Pair ( vr , vr_rest) , Pair(vl , vl_rest) -> Pair(Pair(Symbol "set!", Pair(vr ,Pair (vl, Nil))), create_set_for_letrec vr_rest vl_rest body )
    | never -> raise X_syntax_error

  and create_whatever vars =
    match vars with
    | Nil -> Nil
    | Pair (vr, rest) -> Pair(Pair(vr, Pair(Pair(Symbol("quote") , Pair(Symbol("whatever") , Nil)),Nil)), create_whatever rest)
    | never -> raise X_syntax_error

  and tag_letrec bindings body =
    let all_vars = get_vars bindings in
    let all_vals = get_vals bindings in
    Pair (Symbol "let", Pair((create_whatever all_vars), create_set_for_letrec all_vars all_vals body))

(********************************and*******************************)
  and tag_and x =
    match x with
    | Nil -> Bool (true)
    | Pair (a, Nil)-> a
    | Pair (head, tail) -> Pair (Symbol ("if"), Pair (head, Pair(Pair(Symbol "and", tail), Pair (Bool(false),Nil))))
    | never -> raise X_syntax_error

(********************************all let*******************************)
  and tag_let_star a b =
    match a,b with
    | Nil , Pair(body, Nil) ->  Pair(Symbol "let", Pair(Nil, b))
    | Pair(rib, ribs), b -> (match ribs with
              | Nil -> Pair (Symbol "let", Pair (Pair (rib,ribs), b))
              | _ -> Pair (Symbol "let", Pair (Pair(rib,Nil), Pair(Pair(Symbol("let*"), Pair(ribs, b)), Nil))))
    | never -> raise X_syntax_error

  and tag_let_no_ribs body =
   Pair(Pair (Symbol ("lambda"), Pair(Nil, body)), Nil)

  and tag_let_with_ribs bindings body =
    let all_vars = get_vars bindings in
    let all_vals = get_vals bindings in
    Pair (Pair (Symbol ("lambda"), Pair (all_vars, body)), all_vals)

  and get_vals args =
    match args with
    | Nil ->  Nil
    | Pair (Pair (sym, Pair(value,Nil)), Nil) -> Pair(value, Nil)
    | Pair(Pair(sym , Pair(value,Nil)), args2) -> Pair (value, (get_vals args2))
    | never -> raise X_syntax_error

  and get_vars args =
    match args with
    | Nil ->  Nil
    | Pair (Pair (sym, Pair(value,Nil)), Nil) -> Pair(sym, Nil)
    | Pair(Pair(sym , Pair(value,Nil)), args2) -> Pair (sym, (get_vars args2))
    | never -> raise X_syntax_error

(********************************cond*******************************)
  and tag_cond ribs =
    match ribs with
    | Pair(Pair (Symbol ("else"), thn ),rest)-> Pair(Symbol ("begin"), thn)
    | Pair(Pair(pred, Pair(Symbol("=>") ,proc)),Nil) -> Pair (Symbol "let",
                                                                Pair
                                                                (Pair (Pair (Symbol "value", Pair (pred, Nil)),
                                                                  Pair
                                                                    (Pair (Symbol "f",
                                                                      Pair (Pair (Symbol "lambda", Pair (Nil, proc)),
                                                                      Nil)),
                                                                        Nil)),
                                                                Pair
                                                                  (Pair (Symbol "if",
                                                                    Pair (Symbol "value",
                                                                    Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Nil))),
                                                                  Nil)))
    | Pair(Pair(pred, Pair(Symbol("=>") ,proc)),others) -> Pair (Symbol "let",
                                                                    Pair
                                                                    (Pair (Pair (Symbol "value", Pair (pred, Nil)),
                                                                      Pair
                                                                        (Pair (Symbol "f",
                                                                          Pair (Pair (Symbol "lambda", Pair (Nil, proc)),
                                                                          Nil)),
                                                                        Pair
                                                                        (Pair (Symbol "rest",
                                                                          Pair
                                                                            (Pair (Symbol "lambda",
                                                                              Pair (Nil, Pair (Pair(Symbol "cond", others), Nil))),
                                                                            Nil)),
                                                                        Nil))),
                                                                    Pair
                                                                      (Pair (Symbol "if",
                                                                        Pair (Symbol "value",
                                                                        Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
                                                                          Pair (Pair (Symbol "rest", Nil), Nil)))),
                                                                      Nil)))
    | Pair (Pair(test,thn), Nil) -> Pair ( Symbol ("if") , Pair (test, Pair(Pair(Symbol("begin"),thn) ,Nil)))
    | Pair (Pair(test,thn), x) -> Pair(Symbol ("if"), Pair (test, Pair(Pair(Symbol("begin"),thn) ,Pair(tag_cond x,Nil))))
    | never -> raise X_syntax_error

(********************************quasiquote*******************************)
  and tag_quasiquote x =
    match x with
    | Symbol(y)-> Pair (Symbol("quote"), Pair (x, Nil))
    | Nil-> Pair (Symbol("quote"), Pair (Nil, Nil))
    | Pair(Symbol("unquote"),Pair(sexp,Nil))-> sexp
    | Pair(Symbol("unquote-splicing"),Pair(y, Nil)) -> raise X_syntax_error
    | Pair(a,b) ->( match a,b with
                  | Pair(Symbol ("unquote-splicing"), Pair(rest, Nil)),b -> Pair(Symbol("append"),Pair (rest, Pair ((tag_quasiquote b), Nil)))
                  | a , Pair(Symbol ("unquote-splicing"), Pair(rest, Nil)) -> Pair(Symbol("cons"), Pair ((tag_quasiquote a), Pair(rest,Nil)))
                  | a , b -> Pair( Symbol ("cons"), Pair((tag_quasiquote a), Pair((tag_quasiquote b), Nil))))
     | _ -> x

(********************************define*******************************)
  and tag_define x =
    match x with
    | Pair(Symbol(vr), Pair(vl,Nil)) ->
          (let my_var = (tag_parser (Symbol vr)) in
          match my_var with
            | Var(_)-> Def( my_var, tag_body (Pair(vl,Nil)))
            |_-> raise X_syntax_error)
    | Pair(Pair(vr, arglist),vl)-> tag_parser (Pair(Symbol ("define"), Pair (vr, Pair (Pair(Symbol "lambda", Pair (arglist,vl)), Nil))))
    |_-> raise X_syntax_error

 (********************************lambda*******************************)
  and tag_lambda x =
    match x with
    | Pair(args, body) ->
      if (is_proper_list args)
      then LambdaSimple ((args_to_string_list args) , tag_body body)
      else
        (match args with
        | Symbol(a) -> LambdaOpt([],a, tag_body body)
        |_-> LambdaOpt((args_without_the_last_one args), (last_arg args), tag_body body))
    | _ -> raise X_syntax_error

 (********************************begin*******************************)
    and tag_begin x =
    match x with
    | Pair(sexp1, sexp2) -> if sexp2 = Nil then (List.append [(tag_parser sexp1)] []) else (create_expr_list x)
    | Nil -> [Const(Void)]
    | never -> raise X_syntax_error

 (********************************general*******************************)
  and tag_body x =
    match x with
    | Pair(sexp1, sexp2) -> (match sexp2 with
                                    | Nil-> (tag_parser sexp1)
                                    |_-> Seq (create_expr_list x))
    | Nil -> Const(Void)
    | never -> raise X_syntax_error

  and create_expr_list x =
      match x with
      | Nil -> []
      | Pair (sexp1 , sexp2) -> (tag_parser sexp1):: (create_expr_list sexp2)
      | _ -> [(tag_parser x)]

let start_tag_parser sexpr = tag_parser sexpr;;

let tag_parse_expressions sexpr =
 List.map start_tag_parser sexpr;;

end;; (* struct Tag_Parser *)