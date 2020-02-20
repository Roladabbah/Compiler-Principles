(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)
 let () = Printexc.record_backtrace true;;
#use "reader.ml";;
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
exception X_pair_of_list;;
exception X_error_expand_cond


module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;;
 (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct
(* let tag_parse_expression sexpr = raise X_not_yet_implemented;;
let tag_parse_expressions sexpr =raise X_not_yet_implemented;;
end;; *)

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  



(* work on the tag parser starts here *)

(******HELP FUNCTIONS ********)

let rec check_improper pairs = 
match pairs with 
|Nil-> false
|Pair(a,b)-> (check_improper b)
|_->true;;


let rec  pair_to_list x = 
  (match x with     
  |Pair(expr,Pair(car,cdr))->expr::pair_to_list(Pair(car,cdr))
  |Pair(expr,Nil)->[expr]
  |Nil->[]
  |_->raise X_syntax_error
  ) ;;
   
let rec  check_duplications str_lst = 
  match str_lst with 
      |[]-> false 
      |hd::tl -> match (List.filter (fun a->a = hd) tl) with 
                  |[]->(check_duplications tl)
                  |_ ->true
;;    


let getSeqVarBody body_lst = 
  match body_lst with 
      |[] -> Const Void
      |[hd] -> hd 
      |hd::tl -> Seq body_lst
      ;;

let rec list_of_pair_lambda_body x= 
  match x with  
      |Pair(Pair(Symbol"begin",Pair(a,b)),Nil)->(pair_to_list(Pair(a,b)))
      |Pair(expr,Pair(a,b))->expr::(pair_to_list(Pair(a,b)))
      |Pair(expr,Nil)->[expr] 
      |Nil->[]
      |_ -> raise X_syntax_error



let rec   improper_lst_of_pairs nested_pairs = 
match nested_pairs with 
      |Pair(Symbol a,Symbol b) -> [Symbol a;Symbol b]
      |Pair(a,Pair(car,cdr))->a::(improper_lst_of_pairs (Pair(car,cdr)))
      |_-> raise X_no_match
;;


let rec  check_def lambdas_body_lst = 
match lambdas_body_lst with 
      |[] -> false 
      |Pair (Symbol "define",a)::rest->true
      |Pair (Symbol "begin",body)::rest -> 
              let inside_body = (pair_to_list  body) in 
              let has_inside=(check_def inside_body) in 
              if(has_inside) then true else (check_def rest) 
      |hd::tl -> (check_def tl) 
;;

 
let rec get_str_args symbol_args_lst = 
  match symbol_args_lst with 
      |[Symbol a]-> [a]
      |Symbol a::rest -> [a]@(get_str_args rest)
      |[]-> []
      |_ -> raise X_syntax_error ;;


let rec get_let_vars vv = 
  match vv with
      |Nil -> Nil
      |Pair(Pair(v1,b1),rest)-> Pair(v1,(get_let_vars rest))
      |_->raise X_no_match 
      ;;

let rec get_let_vals vv = 
  match vv with 
      |Nil-> Nil
      |Pair(Pair(v1,Pair(b1,Nil)),rest)-> Pair(b1,(get_let_vals rest))
      |Pair(a,Nil)->(get_let_vals a)
      |_-> raise X_no_match ;;


let rec get_letrec_vars vv = 
  match vv with 
      |Nil -> []
      |Pair (Pair (v1, Pair (b1, Nil)),rest)->v1::(get_letrec_vars rest)
      |_-> raise X_no_match ;;


let rec get_letrec_vals vv = 
  match vv with 
      |Nil -> []
      |Pair (Pair (v1, Pair (b1, Nil)),rest)->b1::(get_letrec_vals rest)
      |_-> raise X_no_match;;


let rec lambda_pairs_to_list x= 
  match x with  
     |Pair(Pair(Symbol"begin",Pair(car,cdr)),Nil)->(pair_to_list (Pair(car,cdr)))
     |Pair(expr,Pair(car,cdr))->expr::(pair_to_list (Pair(car,cdr)))
     |Pair(expr,Nil)->[expr] 
     |Nil->[]
     |_ -> raise X_syntax_error  ;;


let get_lambda_Opt_notVariadic arglst final_body =
     let ls=(improper_lst_of_pairs arglst) in 
     let string_args= (get_str_args ls) in
     let dup = (check_duplications string_args ) in 
     if(dup)  then (raise X_syntax_error) else (
     let rev_list = (List.rev string_args )in
     let last_elemnet = (List.hd rev_list ) in 
     let tl = (List.tl rev_list) in
     let args_no_last= (List.rev tl)in
         LambdaOpt (args_no_last,last_elemnet, final_body));;


let get_lambda_Simple arglst final_body = 
   (*proper *)
     let ls=(pair_to_list arglst) in 
     let string_args= (get_str_args ls) in
     let dup = (check_duplications string_args ) in 
     if(dup) 
     then raise X_syntax_error
     else (LambdaSimple(string_args, final_body));;


(*******  EXPAND FUNCTIONS  ********)

let rec expand_Qqoute x =  
       match x with
     |Pair(Symbol("unquote"),(Pair(y,Nil)))-> y
     (* |Pair(Symbol("quote"),(Pair(y,Nil)))-> y *)
     |Pair(Symbol("unquote-splicing"),a)-> raise X_syntax_error 
     |Symbol(a)->  Pair(Symbol("quote"),(Pair(Symbol(a),Nil)))
     |Nil-> Pair(Symbol("quote"),(Pair(Nil,Nil)))
     |Pair(x_A,x_B)->
         ( match(x_A,x_B)with
          |Pair(Symbol("unquote-splicing"),(Pair(sexpr,Nil))),x_B->
                  Pair(Symbol "append", Pair(sexpr, Pair((expand_Qqoute x_B), Nil)))
          |x_A,Pair (Symbol "unquote-splicing", Pair (sexpr, Nil))->
                  Pair (Symbol "cons", Pair ((expand_Qqoute x_A), Pair (sexpr, Nil)))
          |_->Pair(Symbol("cons"),Pair((expand_Qqoute x_A),Pair((expand_Qqoute x_B),Nil)))
           )
     |exp->exp;; 
     


let rec expand_and s = 
  match s with 
      |[a]-> a
      |a::b::[] ->(Pair(Symbol("if"),Pair(a,Pair(b,Pair(Bool false,Nil)))))
      |a::rest ->  let expanded_rest=(expand_and rest)in
                  (Pair(Symbol("if"),Pair(a,Pair(expanded_rest,Pair(Bool false,Nil)))))
      |_-> raise X_syntax_error 
      ;;

(***********************************EXPAND COND************************************************)
let rec expand_cond s = 
  match s with 
(*last rib is an else rib *)
      |[Pair (Symbol "else", else_expr)]-> Pair(Symbol "begin",else_expr)


(*last rib is with arrow *) 
      |[Pair (test_expr, Pair (Symbol "=>", Pair (then_expr, Nil)))]-> 
        Pair (Symbol "let",
        Pair(Pair (Pair (Symbol "value",Pair (test_expr, Nil)),
        Pair(Pair (Symbol "f",Pair(Pair (Symbol "lambda", Pair (Nil, Pair (then_expr, Nil))),
        Nil)), Nil)), 
        Pair(Pair (Symbol "if",Pair (Symbol "value",Pair (Pair (Pair (Symbol "f", Nil), 
        Pair (Symbol "value", Nil)), Nil))), Nil)))


(*last rib -> normal rib *)
        |[Pair(test,expr_i)]->
           Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),expr_i),Nil)))


(*not last -> else rib *)
        |Pair (Symbol "else", else_expr)::rest ->  Pair(Symbol "begin",else_expr)

(*not last , with arrow *)
        |Pair (test_expr, Pair (Symbol "=>", Pair (then_expr, Nil)))::rest_ribs -> 
          let expanded_rest_ribs = (expand_cond rest_ribs) in 
          Pair (Symbol "let",
          Pair (Pair (Pair (Symbol "value", Pair (test_expr, Nil)),
          Pair (Pair (Symbol "f",Pair (Pair (Symbol "lambda", Pair (Nil, Pair (then_expr, Nil))),
          Nil)),Pair (Pair (Symbol "rest", Pair  (Pair (Symbol "lambda", Pair (Nil, Pair (expanded_rest_ribs, Nil))),
          Nil)), Nil))), Pair (Pair (Symbol "if", Pair (Symbol "value", Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
          Pair (Pair (Symbol "rest", Nil), Nil)))),   Nil)))

(*rib in the middle - then clause with one expr -> no need for begin*)
          |Pair(test,Pair(expr_i,Nil))::rest -> 
                        let expanded=(expand_cond rest) in
                        Pair(Symbol("if"),Pair(test,Pair(expr_i,Pair(expanded,Nil)))) 
            
(*rib in the middle - then clause with more than one expr -> we need begin*)
          |Pair(test,expr_i)::rest_ribs ->       
              let expanded_rest_ribs=(expand_cond rest_ribs) in         
              Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),expr_i),Pair(expanded_rest_ribs,Nil))))

          |_->raise X_syntax_error;;




(*********************EXPAND_LETREC***********************)

let rec make_wtv_pairs vars = 
match vars with 
|[a]-> [Pair (a,Pair (Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil))]
|hd::tl -> Pair (hd,Pair (Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil))::(make_wtv_pairs tl)
|_-> raise X_no_match
;;

let rec make_set_pairs vars vals = 
match (vars,vals) with 
|([v],[b])->  [Pair (Symbol "set!", Pair (v, Pair (b, Nil)))]
|(hd::tl,h::t) -> Pair (Symbol "set!", Pair (hd, Pair (h, Nil)))::(make_set_pairs tl t)
|_-> raise X_no_match
;;

let rec lst_to_pairs lst =
match lst with 
|[]-> Nil 
|hd::tl -> let rest = (lst_to_pairs tl) in 
              Pair(hd,rest)
(* |_-> raise X_no_match_lst_to_pairs *)
;;
let rec expand_letrec vv body = 
let vars = (get_letrec_vars vv ) in 
let vals = (get_letrec_vals vv ) in  
let vars_wtv= (make_wtv_pairs vars) in 
let nested_wtv = (lst_to_pairs vars_wtv) in  
let set_pairs = (make_set_pairs vars vals) in 
let body_lst = (pair_to_list body) in
let concat = set_pairs@body_lst in
let final_body = (lst_to_pairs concat) in 
Pair((Symbol("let")),(Pair(nested_wtv,final_body)));;



(******************************************parsers*************************************)
let parse_variable x = match x with 
    |Symbol(x)->
    let is_mem = (List.mem x reserved_word_list ) in 
        if(is_mem ) 
        then raise X_no_match 
        else (Var x) 
    |_->raise X_syntax_error;;



let rec parse_const s = 
  match s with 
(**** self eval consts ****)
        |Nil -> Const (Void)
        |Number(a)->Const(Sexpr(s))
        |Char(a) ->Const(Sexpr(s))
        |Bool(a)-> Const(Sexpr(s))
        |String(a)->Const(Sexpr(s))
        |TagRef x -> Const(Sexpr(s))
        |TaggedSexpr (x, sexpr)-> Const(Sexpr(TaggedSexpr(x,sexpr)))
        |_-> raise X_no_match 



and parse_qoute_forms s = 
  match s with 
        |Pair(Symbol("quote"), Pair(sexpr, Nil))  -> Const(Sexpr(sexpr))
        |Pair(Symbol("unquote"), Pair(sexpr, Nil))->  Const(Sexpr(sexpr))
        |Pair(Symbol "quasiquote", Pair (sexpr, Nil))->(tag_parse (expand_Qqoute sexpr))
        |Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil))-> raise X_syntax_error
        | _-> raise X_no_match 



and parse_define s =
  match s with 
        |Pair(Symbol("define"),Pair(Pair(var,arglst),body))
            ->(parse_define (Pair(Symbol"define", Pair(var,Pair(Pair(Symbol "lambda" ,Pair(arglst,body)),Nil)))))
        |Pair(Symbol("define"),Pair(var,Pair(value,Nil)))
            ->let parsed_var = (parse_variable var) in 
            Def(parsed_var,(tag_parse value))
        | _ -> raise X_no_match 


and parse_if s = 
  match s with 
        |Pair (Symbol "if", Pair (cond_exp, Pair (then_exp, Nil)))-> 
          let parsed_test = (tag_parse cond_exp) in
          let parsed_then = (tag_parse then_exp) in
          let parsed_else = (tag_parse Nil) in
        If(parsed_test,parsed_then,parsed_else)

        |Pair (Symbol "if", Pair (cond_exp, Pair (then_exp, Pair (else_exp, Nil))))->
          let parsed_test = (tag_parse cond_exp) in 
          let parsed_then = (tag_parse then_exp) in 
          let parsed_else = (tag_parse else_exp) in 
              If(parsed_test,parsed_then,parsed_else)

        |_-> raise X_no_match 



and parse_lambda x = 
  match x with 
 (*variadic *)
        |Pair (Symbol "lambda" ,Pair (Symbol (a),body))->
        let lst = (pair_to_list body) in
          if (check_def lst )
          then (raise X_syntax_error) 
          else(
          let lambdas_body_lst=(list_of_pair_lambda_body body) in 
          match lambdas_body_lst with 
          |[] -> raise X_syntax_error
          |_->
          let parsedbody= (List.map tag_parse  lambdas_body_lst) in
          let final_body = (getSeqVarBody parsedbody)in
          LambdaOpt ([],a , final_body)) 

 (*not variadic *)
        |Pair (Symbol "lambda", Pair (arglst,body))-> 
          let lst = (pair_to_list body) in
            if (check_def lst )
              then raise X_syntax_error 
              else      
              (
                let lambdas_body_lst= (list_of_pair_lambda_body body) in
                match lambdas_body_lst with 
                  |[]-> raise X_syntax_error
                  |_->
                    let parsedbody= (List.map tag_parse lambdas_body_lst) in
                    let final_body = (getSeqVarBody parsedbody)in
                    let im_prop = (check_improper arglst) in 
                    match im_prop with 
                    |true-> (get_lambda_Opt_notVariadic arglst final_body)
                    |false -> (get_lambda_Simple arglst final_body)
              )
        |_->raise X_no_match 


and parse_or s = 
  match s with 
        |Pair (Symbol "or",sexpr_list)-> 
          (match sexpr_list with 
          |Nil -> tag_parse (Bool false)
          |_-> let lst = (pair_to_list sexpr_list) in 
              let parsed_lst = (List.map tag_parse lst) in 
              (match parsed_lst with 
              |[element]->element
              |_-> Or(parsed_lst))
          )
        |_-> raise X_no_match 



and parse_cond s =
  match s with 
        |Pair (Symbol "cond",rest) ->
                let cond_ribs = (pair_to_list  rest) in
                let expanded = (expand_cond cond_ribs) in
                (tag_parse expanded)
        |_-> raise X_no_match 
 


and parse_let s = 
  match s with 
        |Pair (Symbol "let", Pair (vars_vals_pairs,body))->
            let vars = (get_let_vars vars_vals_pairs) in 
            let vals = (get_let_vals vars_vals_pairs) in 
          (parse_applic(Pair((Pair(Symbol "lambda",Pair(vars,body))),vals)))
        |_->raise X_no_match 



and parse_set s = 
  match s with 
        |Pair (Symbol "set!", Pair (Symbol var_name,Pair(sexp,Nil)))->
                let parsed_var= (tag_parse (Symbol var_name) ) in
                let parsed_sexp = (tag_parse sexp) in 
                (Set (parsed_var,parsed_sexp)) 
        |_-> raise X_no_match



and parse_begin s = 
  match s with 
        |Pair (Symbol "begin",Nil) ->( tag_parse Nil )
        |Pair (Symbol "begin",rest)-> 
              let rest_lst = (pair_to_list  rest) in 
              let parsed_rest = (List.map tag_parse rest_lst) in 
                  (getSeqVarBody parsed_rest)
        |_-> raise X_no_match 



and parse_and s = 
  match s with 
        |Pair (Symbol "and",sexpr_lst)->
              (match sexpr_lst with 
              |Nil->tag_parse (Bool true)
              |_-> let lst =(pair_to_list sexpr_lst) in
                   let expanded=(expand_and lst)  in 
                   ( tag_parse expanded )
              )
        |_->raise X_no_match 



and parse_applic s= 
  match s with 
        |Pair(proc,sexprs)->
              let sexpr_lst =(pair_to_list  sexprs) in  
              let exprs= (List.map tag_parse sexpr_lst) in 
              let parsed_proc= (tag_parse proc) in 
              Applic(parsed_proc,exprs)
        |_-> raise X_no_match 



and parse_let_star s = 
  match s with 
        (*two basic cases*)
        |Pair (Symbol "let*",Pair (Nil, body))
              ->parse_let(Pair (Symbol "let", Pair(Nil,body)))
        |Pair (Symbol "let*",Pair (Pair (Pair (v1, Pair (b1, Nil)), Nil), body))
              ->parse_let(Pair (Symbol "let", Pair(Pair (Pair (v1, Pair (b1, Nil)), Nil),body)))
        (*genarally*)
        |Pair (Symbol "let*",Pair (Pair (Pair (v1, Pair (b1, Nil)), rest_vv),body))
              ->parse_let((Pair (Symbol "let",Pair(Pair(Pair( v1,Pair (b1, Nil)),Nil),
          Pair(Pair(Symbol "let*",Pair(rest_vv,body)),Nil)))))
        |_->raise X_no_match 



and parse_letrec s =
  match s with 
        |Pair (Symbol "letrec", Pair (Nil, body))->
            let expanded = Pair(Symbol "let",Pair(Nil,body)) in 
            (tag_parse expanded)
        |Pair (Symbol "letrec", Pair (vars_vals, body))->
            let expanded_letrec = (expand_letrec vars_vals body ) in
            (tag_parse expanded_letrec)
        |_-> raise X_no_match 



and tag_parse x =  disj_list [parse_const;
                              parse_qoute_forms;
                              parse_define;
                              parse_if;
                              parse_lambda;
                              parse_or;
                              parse_cond;
                              parse_let;
                              parse_set;
                              parse_begin;
                              parse_and;
                              parse_applic;
                              parse_let_star;
                              parse_letrec;
                              parse_variable;] x ;; 



let tag_parse_expression sexpr = (tag_parse sexpr);;
let tag_parse_expressions sexpr =( List.map tag_parse sexpr);;
end;;

 (* struct Tag_Parser *)
 
