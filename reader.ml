#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Fraction of int * int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let make_paired nt_left nt_right nt=
  let nt = caten nt_left nt in
  let nt = pack nt (function(_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function(e, _) -> e) in
  nt;;

let nt_dot = char '.' ;;

let nt_comma = char ',';;

let nt_left_paren = char '(';;

let nt_right_paren = char ')';;

let nt_hashtag = char '#';;

let nt_semicolon = char ';';;

let nt_minus = char '-';;

let nt_plus = char '+';;

let nt_back_slash = char '/';;

let nt_newline = char '\n';;

let nt_slash = char (char_of_int 92);;

let nt_punc = one_of "!$^*-_=+<>/?:" ;;

let nt_all = star (const (fun ch ->  ch != '\n')) ;;

let nt_whitespaces = star (char ' ');;

let digit = range '0' '9';;

let natural_numbers = (plus digit);;


(*from practice *)
let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;

let nt_one_letter = pack (range_ci 'a' 'z') (fun ch -> lowercase_ascii ch);;

let nt_letters = star (range_ci 'a' 'z');;

let length l =
  let rec f n = function
    | []-> n
    | _::t -> f (n+1) t
  in f 0 l;;

  let nt_line_comment =
    let nt = pack nt_end_of_input (fun a -> ' ') in
    let nt = caten (caten nt_semicolon nt_all) (disj nt nt_newline) in
    let nt = pack nt (fun _ -> Nil) in
    make_spaced nt ;;

(***********************boolean parsing 3.3.1******************************)

let tok_bool =
  let t_parse = pack (char_ci 't') (fun t -> true) in
  let f_parse = pack (char_ci 'f') (fun f -> false) in
  let nt = pack (caten nt_hashtag (disj t_parse f_parse)) (fun (_, b) ->  Bool b) in
  nt;;


(***********************symbol parsing 3.3.3******************************)

let tok_symbol =
  let nt = disj_list [nt_one_letter; nt_punc; digit; nt_dot] in
  let nt = plus nt in
  let nt = pack nt (fun l ->
                    if (length l)==1 && (list_to_string l) = "."
                    then raise X_no_match
                    else Symbol (list_to_string l)) in nt;;

(***********************number parsing 3.3.2******************************)

let rec gcd x y =
  match (x mod y) with
    0 -> y
    | r -> gcd y r;;

let nt_integer =
  let nt_op = disj nt_minus nt_plus in
  let full_number  = not_followed_by natural_numbers (diff tok_symbol digit) in
  let make_it_signed = pack (caten nt_op full_number) (fun (sign, num)->  match sign with
    | '-' -> Fraction (int_of_string (list_to_string num)*(-1), 1)
    | _ -> Fraction (int_of_string (list_to_string num), 1)) in
  let unsigned = pack full_number (fun n ->  Fraction (int_of_string (list_to_string n), 1)) in
  let nt = disj make_it_signed unsigned in
  nt;;


let nt_fraction =
  let nt_op = disj nt_minus nt_plus in
  let unsigned_full_number = not_followed_by (caten (caten natural_numbers nt_back_slash) natural_numbers) (diff tok_symbol digit) in
  let make_it_signed = pack (caten nt_op unsigned_full_number) (fun (sign, ((numi,_),dom))->

          let int_numi = (int_of_string(list_to_string numi)) in
          let int_domi = (int_of_string(list_to_string dom)) in
          let my_gcd = gcd int_numi int_domi in
          match sign with
          | '-'-> Fraction ((int_numi/my_gcd)*(-1), (int_domi/my_gcd))
          | _ -> Fraction ((int_numi/my_gcd), (int_domi/my_gcd))) in

  let not_signed_frac = pack unsigned_full_number (fun (((numi,_),dom))->
            let int_numi = (int_of_string(list_to_string numi)) in
            let int_domi = (int_of_string(list_to_string dom)) in
            let my_gcd = gcd int_numi int_domi in
            Fraction ((int_numi/my_gcd), (int_domi/my_gcd))) in

  let nt = disj not_signed_frac make_it_signed
  in nt;;


let nt_float =
  let nt_op = disj nt_minus nt_plus in
  let nt_diff = diff tok_symbol (char_ci 'e') in
  let parse_digits = not_followed_by (caten (caten  natural_numbers nt_dot) natural_numbers) nt_diff in
  let unsigned_full_number  = pack parse_digits (fun (((lhs,dot),rhs))->
  float_of_string((list_to_string lhs) ^ "." ^ (list_to_string rhs))) in
  let make_it_signed = pack (caten nt_op unsigned_full_number) (fun (sign, n) -> if (sign = '-') then (-1.0) *. n
                                                  else n) in
  let nt = disj make_it_signed unsigned_full_number in
  let nt = pack nt (fun a -> Float a) in nt;;

(***********************scientific_notation parsing 4.1******************************)

let nt_int =
  let nt_op = disj nt_minus nt_plus in
  let full_number  = not_followed_by natural_numbers (diff tok_symbol (disj (char_ci 'e') digit)) in
  let make_it_signed = pack (caten nt_op full_number) (fun (sign, num)->  match sign with
    | '-' -> "-"^(list_to_string num)
    | _ -> list_to_string num) in
  let unsigned = pack full_number (fun n ->(list_to_string n)) in
  let nt = disj make_it_signed unsigned in
  nt;;

let nt_float_number =
  let nt_op = disj nt_minus nt_plus in
  let nt_diff = diff tok_symbol (char_ci 'e') in
  let parse_digits = not_followed_by (caten (caten  natural_numbers nt_dot) natural_numbers) nt_diff in
  let unsigned_full_number  = pack parse_digits (fun (((lhs,dot),rhs))->
  (list_to_string lhs) ^ "." ^ (list_to_string rhs)) in
  let make_it_signed = pack (caten nt_op unsigned_full_number) (fun (sign, n) -> if (sign = '-') then "-"^n else n) in
  let nt = disj make_it_signed unsigned_full_number in
  nt;;


let scientific_notation =
  let nt = disj_list [nt_int; nt_float_number] in
  let parse_e = char_ci 'e' in
  let nt = pack (caten nt (caten parse_e nt)) (fun (lhs,(e,rhs))-> Float (float_of_string (lhs^"e"^rhs))) in
    nt;;


  let tok_num =
    pack (disj_list [scientific_notation; nt_float; nt_fraction; nt_integer])
     (fun a -> Number a);;


(***********************string parsing 3.3.4******************************)

let par_str_literal_char =
  let nt_quotes = char (char_of_int 34) in
  let nt = diff nt_any (disj nt_slash nt_quotes) in nt;;

let par_str_meta_char =
  disj_list [
          pack (word "\\\\") (fun _ -> '\092');
          pack (word "\\\"") (fun _ -> '\034');
          pack (word "\\t") (fun _ -> '\009');
          pack (word "\\f") (fun _ -> '\012');
          pack (word "\\n") (fun _ -> '\010');
          pack (word "\\r") (fun _ -> '\013')
          ];;

let parse_stringChar =
    disj par_str_literal_char par_str_meta_char;;

let tok_string =
  let nt_quotes = char (char_of_int 34) in
  let nt = caten  (caten (nt_quotes) (star parse_stringChar)) nt_quotes in
  pack nt (fun (((_, a), _)) -> String (list_to_string a));;


(***********************char parsing 3.3.5******************************)

let nt_named_chars =
  let nt = caten nt_hashtag nt_slash in
  let next_nt = disj_list [
    pack (word_ci "nul") (fun a -> '\000');
    pack (word_ci "newline") (fun a -> char_of_int 10);
    pack (word_ci "return") (fun a -> '\r');
    pack (word_ci "tab") (fun a -> '\t');
    pack (word_ci "page") (fun a -> '\012');
    pack (word_ci "space") (fun a -> ' ')
    ] in
    pack (caten nt next_nt) (fun ((_,_), c) -> Char c);;

let nt_visible_chars =
  let nt = caten nt_hashtag nt_slash in
  let next_nt = const (fun ch ->  ch > ' ' && ch <= (char_of_int 255)) in
  pack (caten nt next_nt) (fun ((_,_), c) -> Char c);;


let tok_char =
  disj nt_named_chars nt_visible_chars;;

(***********************sexprs parsing******************************)

let get_whitespaces = pack nt_whitespace (fun _ -> Nil);;

let rec sexprs_parser str =
  let all_exps = disj_list [tok_bool; tok_num; tok_symbol; tok_string; tok_char;
                            nt_list; nt_dotted_list; nt_quoted; nt_quasiquoted;
                            nt_unquoted; nt_unquoted_and_spliced; nt_comment_sexp; nt_nil] in
  (ignore_whitespaces_or_comments all_exps) str

  and nt_list s =
      let parsed_list = caten nt_left_paren (caten (star sexprs_parser) nt_right_paren) in
      let list_as_pair = pack parsed_list (fun (_,(l,_))-> if (l = []) then Nil else List.fold_right (fun se1 se2-> Pair (se1, se2)) l Nil)
      in list_as_pair s

  and nt_dotted_list s =
      let body_of_list = caten (plus sexprs_parser) (caten nt_dot sexprs_parser) in
      let parsed_list = caten nt_left_paren (caten body_of_list nt_right_paren) in
      let dotted_list_as_pair = pack parsed_list
          (fun (_,((lhs, (_, rhs)),_)) -> List.fold_right (fun se1 se2 -> Pair(se1, se2)) lhs rhs)
      in dotted_list_as_pair s

  and nt_quoted s =
      let nt_quote = char (char_of_int 39) in
      let parsed_quote = caten nt_quote sexprs_parser in
      let parsed_quote = pack parsed_quote (fun (_, s)-> Pair (Symbol "quote", Pair (s, Nil)))
      in parsed_quote s

  and nt_quasiquoted s =
      let nt_quasiquote = char (char_of_int 96) in
      let parsed_quasiquote = caten nt_quasiquote sexprs_parser in
      let parsed_quasiquote = pack parsed_quasiquote (fun (_,s)-> Pair (Symbol "quasiquote", Pair (s, Nil)))
      in parsed_quasiquote s

  and nt_unquoted s =
      let parsed_unquote = caten (char ',') sexprs_parser in
      let parsed_unquote = pack parsed_unquote (fun (_,s)-> Pair (Symbol "unquote", Pair (s, Nil)))
      in parsed_unquote s

  and nt_unquoted_and_spliced s =
      let parsed_unquoted_and_spliced = caten (caten (char ',') (char '@')) sexprs_parser in
      let parsed_unquoted_and_spliced = pack parsed_unquoted_and_spliced (fun (_,s)-> Pair (Symbol "unquote-splicing", Pair (s, Nil)))
      in parsed_unquoted_and_spliced s

  and nt_comment_sexp s =
    let nt = caten (caten nt_hashtag nt_semicolon) sexprs_parser in
    let nt = pack nt (fun _ -> Nil)
    in nt s

  and nt_nil s =
    let nt = caten nt_left_paren (caten (star (disj_list [get_whitespaces; nt_comment_sexp; nt_line_comment])) nt_right_paren) in
    let nt = pack nt (fun _ -> Nil)
    in nt s

  and ignore_whitespaces_or_comments s =
    let all_ignored = disj_list [nt_comment_sexp; nt_line_comment; get_whitespaces] in
    let make_commented nt = make_paired (star all_ignored) (star all_ignored) nt in
    make_commented s;;

  let read_sexprs string =
      let (result , s) = (star sexprs_parser) (string_to_list string) in result ;;

end;; (* struct Reader *)