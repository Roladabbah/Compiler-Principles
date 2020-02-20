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
end;;

module Semantics : SEMANTICS = struct
(* code should be written here ! *)

(* struct Semantics *)

(***************  lexical address ***************** *)
let rec get_minor var list = 
let hd= (List.hd list) in 
let tl =(List.tl list) in 
let ans =(String.equal var hd) in 
if(ans) 
then 0 
else  (1+(get_minor var tl) ) 
;;

(* x:          the var that we want to change to var'
arglists:    list of stringlists , each list is a arglist for some lambda 
lambda_num :       contains the major of the var (nested lambdas or (lists in stringlists) ) *)
let rec get_var_tag (x,lambda_num,arglists)=
  match arglists with
  | []-> VarFree(x)
  | _->(
    let inlist=(List.mem x (List.hd arglists) ) in
    match inlist with
    | true->( 
      if(lambda_num=(-1)) 
      then VarParam(x,(get_minor x (List.hd arglists)))
      else VarBound(x,lambda_num,(get_minor x (List.hd arglists)))
    )
    | false-> (
      let tl =List.tl arglists in 
       get_var_tag (x,lambda_num+1,tl)
    )
  );;

(*we are interested of every occurrence of Var*)
let rec get_lexical_addresses (expr ,arglists) = 
match expr with 
|Const(x)->
      Const'(x)
|Var (x) ->      
      Var'(get_var_tag (x,-1,arglists))
|If(test_expr,then_expr,else_expr)-> 
      If'((get_lexical_addresses (test_expr, arglists)),
      (get_lexical_addresses (then_expr, arglists)),
      (get_lexical_addresses( else_expr, arglists)))
|Seq(exprList)-> 
      let lst = (List.map (fun(x)->(x, arglists) )exprList) in
      Seq'(List.map get_lexical_addresses lst)
|Set(exprvar,exprval)-> 
      Set'((get_lexical_addresses (exprvar, arglists)),
      (get_lexical_addresses( exprval, arglists)))
|Def(exprvar,exprval)->
      Def'((get_lexical_addresses (exprvar, arglists)),
      (get_lexical_addresses( exprval, arglists)))
|Or(exprList)->  
      let lst = (List.map (fun(x)->(x, arglists)) exprList) in 
      Or'(List.map get_lexical_addresses lst)
|LambdaSimple(strlist,expr)->
      let lst =(strlist::arglists) in
      LambdaSimple'(strlist,get_lexical_addresses(expr,lst))
|LambdaOpt (strlist,str,expr) -> 
      let lst = ((strlist@[str])::arglists) in 
      LambdaOpt'(strlist,str,get_lexical_addresses(expr,lst))
|Applic(expr,exprList)->    
      let lst = (List.map (fun(x)->(x, arglists)) exprList) in 
      let lst2= (List.map get_lexical_addresses  lst ) in
      Applic'((get_lexical_addresses (expr, arglists)), lst2);; 



(**************tail Calls (applic) *******************)

let rec work_with_applics (expr,covered_by_lambda) = 
match expr with 
|If'(test_expr,then_expr,else_expr)->
      (match covered_by_lambda with 
      |false-> If'(work_with_applics(test_expr,false),
                   work_with_applics(then_expr,false),
                   work_with_applics(else_expr,false))
      |true-> If' (work_with_applics(test_expr,false),
                   work_with_applics(then_expr,true),
                   work_with_applics(else_expr,true))
      )
|Seq'(exprlist)-> 
      (match covered_by_lambda with 
      |false->Seq' (List.map work_with_applics (List.map (fun(x)->(x,false)) exprlist))
      |true-> let with_out_last= (List.rev (List.tl (List.rev exprlist))) in
              let last = (List.hd (List.rev exprlist)) in
              let falsse_pairs = (List.map  (fun (x)->(x,false)) with_out_last) in 
              let true_last = (last,true) in 
              let falsse_pairs_result =(List.map work_with_applics falsse_pairs) in 
              let concat = falsse_pairs_result@[work_with_applics true_last] in 
                       Seq' (concat)
      )
| Set'(exprvar,exprval)-> Set'(
                          work_with_applics(exprvar,false),
                          work_with_applics(exprval,false))
| Def'(exprvar,exprval)-> Def'(
                          work_with_applics(exprvar,false),
                          work_with_applics(exprval,false))
| Or'(exprlist)->(
    match covered_by_lambda with
    | false-> 
            let ls = (List.map  (fun (x)->(x,false)) exprlist) in 
            Or'(List.map work_with_applics ls)
    | true->let with_out_last = (List.rev (List.tl (List.rev exprlist))) in 
            let last = (List.hd (List.rev exprlist)) in 
            let falsse_pairs = (List.map  (fun (x)->(x,false))with_out_last) in 
            let falsse_pairs_result =(List.map work_with_applics falsse_pairs) in
            let last_result = (work_with_applics(last,true)) in 
             Or' (falsse_pairs_result@ [last_result])
  )
| LambdaSimple'(parmslist,expr)->
              LambdaSimple'(parmslist,work_with_applics(expr,true))
| LambdaOpt'(parmslist,str,expr)->
              LambdaOpt'(parmslist,str,work_with_applics(expr,true))
| Applic' (expr,exprlist)-> 
  (match covered_by_lambda with
   | false-> let exprlist_pairs = (List.map  (fun (x)->(x,false)) exprlist) in 
             let pairs_result = (List.map work_with_applics exprlist_pairs) in 
             Applic'(work_with_applics (expr,false), pairs_result)
   | true->  let exprlist_pairs = (List.map  (fun (x)->(x,false)) exprlist) in 
             let pairs_result = (List.map work_with_applics exprlist_pairs) in 
             ApplicTP'(work_with_applics (expr,false), pairs_result)
  )
| _-> expr;;

(**************   BOXING   *****************)

(*we are interested about every occurrence of varbound/varpram
  numberlist - contains the path of the nested lambdas*)
let check_get parm body =
  let last = ref 0 in
  let unique = 
     fun () -> incr last ; !last in
  
  let rec check_get_helper parm body lambdas_path  = 
    match body with
  | If' (expr1, expr2, expr3)-> (check_get_helper parm expr1 lambdas_path)@
                                (check_get_helper parm expr2 lambdas_path)@
                                (check_get_helper parm expr3 lambdas_path)
  | Def' (expr1, expr2) ->      (check_get_helper parm expr1 lambdas_path)@
                                (check_get_helper parm expr2 lambdas_path)
  | Seq' exprlist -> 
          let exprlist_result = (List.map (fun(body)-> check_get_helper parm body lambdas_path)  exprlist) in
            (List.flatten  exprlist_result)
  
  | Set' (Var'(var),expr)->      (check_get_helper parm expr lambdas_path)
  | BoxSet' (var, expr) ->       (check_get_helper parm expr lambdas_path)
  | Or' exprlist ->
          let exprlist_result = (List.map (fun(body)-> check_get_helper parm body lambdas_path)  exprlist) in
          (List.flatten exprlist_result)
  | Applic' (op, exprlist) | ApplicTP' (op, exprlist) -> 
          let exprlist_result = (List.map (fun(body)-> check_get_helper parm body lambdas_path)  exprlist) in 
          let flatten_ls =  (List.map List.flatten  exprlist_result  ) in 
          let op_result = (check_get_helper parm op lambdas_path) in 
          (op_result@flatten_ls)
  | LambdaSimple' (parmlist,body1)-> 
          if (List.mem parm parmlist) 
          then ([]) 
          else let num = unique() in
          (check_get_helper parm body1 (num::lambdas_path))
  | LambdaOpt' (parmlist,opt,body1)-> 
          if (List.mem parm (opt::parmlist)) 
          then ([]) 
          else 
          let num = unique() in 
          (check_get_helper parm body1 (num::lambdas_path))
  | Var'(VarBound(name,minor,major))-> 
          if (parm=name) 
          then [lambdas_path] 
          else ([])
  | Var'(VarParam(name,minor))-> 
          if (parm=name) 
          then [lambdas_path] 
          else ([])
  | _->[] in

  
  (check_get_helper parm body [0] )
  ;;


(*we are interested in every occurence for Set'*)
  let check_set parm body =
    let last = ref 0 in 
    let unique = 
     fun () -> incr last ; !last in
    
    let rec check_set_helper parm body numberlist  = 
      match body with
    | If' (expr1, expr2, expr3)-> (check_set_helper parm expr1 numberlist)@
                                  (check_set_helper parm expr2 numberlist)@
                                  (check_set_helper parm expr3 numberlist)
    | Def' (expr1, expr2) ->      (check_set_helper parm expr1 numberlist)@
                                  (check_set_helper parm expr2 numberlist)
    | Seq' exprlist -> 
            let exprlist_result = (List.map (fun(body)-> check_set_helper parm body numberlist)  exprlist) in 
            (List.flatten  exprlist_result)
    | Set' (Var'(VarBound(name,minor,major)),expr)-> 
            let expr_result = (check_set_helper parm expr numberlist) in 
            if (parm=name) 
            then ([numberlist]@ expr_result) 
            else (expr_result)
    | Set' (Var'(VarParam (name,major)),expr)-> 
            let exprlist_result = (check_set_helper parm expr numberlist) in 
            if (parm=name) 
            then ([numberlist]@ exprlist_result) 
            else (exprlist_result)
    | Set' (Var'(VarFree(x)),expr)->(check_set_helper parm expr numberlist)
    | BoxSet' (var, expr) ->        (check_set_helper parm expr numberlist)
    | Or' exprlist -> 
            let exprlist_result= (List.map (fun(body)-> check_set_helper parm body numberlist)  exprlist) in
            (List.flatten exprlist_result)
    | Applic' (op, exprlist) | ApplicTP' (op, exprlist) -> 
            let exprlist_result = (List.map (fun(body)-> check_set_helper parm body numberlist)  exprlist) in 
            let flatten_result = (List.map List.flatten  exprlist_result) in  
            let op_result = (check_set_helper parm op numberlist) in 
           (op_result@flatten_result)
    | LambdaSimple' (parmlist,body1)-> 
            if (List.mem parm parmlist  ) 
            then ([]) 
            else let num = unique() in(check_set_helper parm body1 (num::numberlist))
    | LambdaOpt' (parmlist,opt,body1)-> 
            if (List.mem parm (opt::parmlist)  ) 
            then ([]) 
            else let num = unique() in (check_set_helper parm body1 (num::numberlist))
    | Var'(VarBound(name,minor,major))-> 
            if (parm=name) 
            then [] 
            else ([])
    | Var'(VarParam(name,minor))-> 
            if (parm=name) 
            then [] 
            else ([])
    | _->[] in
    
    (check_set_helper parm body [0] )
    ;;

let  check_common_ancestor (path1,path2)  =
if(path1 =[] ||path2=[]) then true else 
(  let same_lambda =(List.hd path1 != List.hd path2)  in
  let rec help_common_ancestor (path1,path2) =
  match (path1=[] || path2=[]) with 
   |true-> true
   |false->(
          let hd = (List.hd path1 = List.hd path2) in
          match hd with 
          |true -> false 
          |false -> (let tl1=List.tl path1 in 
                    let tl2=List.tl path2 in 
                     help_common_ancestor(tl1,tl2))
    ) in
(same_lambda && help_common_ancestor (List.tl (List.rev path1),List.tl (List.rev path2))));;

let check_if_should_box_parm (parm ,body)=
  let set_result = (check_set parm body) in
  let get_result =(check_get parm body) in 
  let setlist= List.filter (fun(x)->x!=[]) set_result  in
  let getlist= List.filter (fun(x)->x!=[]) get_result  in
  let list_of_pairs = List.concat (List.map (fun(x)->List.map (fun(y)->(x,y)) getlist) setlist) in
        if (ormap check_common_ancestor list_of_pairs) then parm else "no need for boxing!!";;

let get_params_to_box parmslist body=
  let pairs_param_body= (List.map (fun(x)-> (x,body)) parmslist) in 
  let returned_vals= (List.map check_if_should_box_parm pairs_param_body) in
 (List.filter (fun(x)->x != "no need for boxing!!" ) returned_vals )


let rec get_params_to_update params_need_box indexed_params =
  match  (indexed_params = []) with 
  |true-> [] 
  |false-> (
      let (param,index)=(List.hd indexed_params) in
      let ismember= (List.mem param params_need_box) in 
      let tl_indexed = (List.tl indexed_params) in 
        match ismember with 
        |true->((param,index)::(get_params_to_update params_need_box tl_indexed))
        |false->((get_params_to_update params_need_box tl_indexed))
    )
  ;;

let get_indexes params_lst_length=
  let rec get_index_helper num=
   ( match num with 
    |(-1)-> [] 
    |_-> (get_index_helper(num-1)@[num])) in
  get_index_helper (params_lst_length-1);;

let extend_body params paramstobox =
    let indexed_lst = (get_indexes (List.length params)) in 
    let indexed_params = (List.map2 (fun a b->(a,b)) params indexed_lst) in
    let indexed_params_need_updates= get_params_to_update paramstobox indexed_params in
   ( List.map (fun (var,index)->
    Set' (Var'(VarParam(var,index)),Box'(VarParam(var,index)))) indexed_params_need_updates)
  ;;




let rec box_help_func (expr,stringList) =
match expr with 
| Const' _ -> expr
|Var'(VarFree(_))->expr
|Box' _ ->expr
|BoxGet' _ ->expr
|Var'(VarBound (var_name,minor,major))->
    let inlist = (List.mem var_name stringList) in 
    (match inlist with 
    |true-> (BoxGet' (VarBound(var_name,minor,major)))
    |false-> expr)
|Var'(VarParam(var_name,minor))-> 
    let inlist= (List.mem var_name stringList) in
   ( match inlist with 
    |true-> (BoxGet'(VarParam(var_name,minor)))
    |false-> expr)

|Def'(expr_var,expr_val)->
    let boxed_var =box_help_func(expr_var,stringList) in 
    let boxed_val =box_help_func(expr_val,stringList) in 
    Def'(boxed_var,boxed_val)
|If'(expr_test,expr_then,expr_else)->
    let boxed_test = (box_help_func(expr_test,stringList)) in 
    let boxed_then = (box_help_func(expr_then,stringList)) in
    let boxed_else = (box_help_func(expr_else,stringList)) in 
     If'(boxed_test,boxed_then,boxed_else)

|Seq'(exprlist)->
    let pairs =(List.map (fun(x)->(x,stringList)) exprlist) in 
    Seq' (List.map box_help_func pairs)
|BoxSet'(expr_var,expr_val)->
    let boxed_val=box_help_func(expr_val,stringList) in 
    BoxSet'(expr_var,boxed_val)
|Set'(Var'(VarParam(var_name,minor)),expr_val)->
    let boxed_exprval = (box_help_func (expr_val,stringList)) in
    let inlist =  (List.mem  var_name stringList) in 
    (match inlist with 
    |true-> BoxSet'(VarParam(var_name,minor),boxed_exprval) 
    |false-> Set'(Var'(VarParam(var_name,minor)),boxed_exprval))
|Set'(Var'(VarBound(var_name,minor,major)),expr_val)->
    let inlist =  (List.mem  var_name stringList) in 
   ( match inlist with 
    |true->  BoxSet'(VarBound(var_name,minor,major),box_help_func (expr_val,stringList)) 
    |false-> Set'(Var'(VarBound(var_name,minor,major)),box_help_func (expr_val,stringList)))
|Set'(Var'(VarFree(var_name)),expr_val)->
    let boxed_val = box_help_func (expr_val,stringList) in 
    Set'(Var'(VarFree(var_name)),boxed_val)
| Or'(exprlist)-> 
    let pairs = (List.map  (fun(x)->(x,stringList)) exprlist)  in 
    Or' (List.map box_help_func pairs)


|LambdaSimple'(params,body)-> 
    let filtered_stringList = (List.filter (fun(x) -> not (List.mem x params)) stringList) in
    let paramstobox= (get_params_to_box params body) in
    let make_updates= (extend_body params paramstobox) in
    let new_stringList = (paramstobox@filtered_stringList) in 
    let box_inner_body= box_help_func (body ,new_stringList) in
    let updated_body = (make_updates@[box_inner_body]) in
            (match updated_body with
              | []-> LambdaSimple'(params,Const' Void)
              | one_expr::[]->LambdaSimple'(params,one_expr)
              | more->LambdaSimple'(params,Seq' more))
|LambdaOpt'(params,str,body)-> 
  let filtered_stringList = (List.filter (fun(x) -> not (List.mem x params)) stringList) in
  let paramstobox= get_params_to_box (str::params) body in
  let make_updates= extend_body (params@[str])  paramstobox in
  let new_stringList= (paramstobox@filtered_stringList) in 
  let box_inner_body= box_help_func (body ,new_stringList) in
  let updated_body = (make_updates@[box_inner_body]) in
            (match updated_body with
              | []-> LambdaOpt'(params,str,Const' Void)
              | one_expr::[]->LambdaOpt'(params,str,one_expr)
              | more->LambdaOpt'(params,str,Seq' more))


| Applic'(expr,exprlist) -> 
    let boxed_expr = box_help_func (expr,stringList) in 
    let boxed_exprlist = (List.map box_help_func (List.map  (fun(x)->(x,stringList)) exprlist)) in 
    Applic'(boxed_expr,boxed_exprlist)
| ApplicTP'(expr,exprlist)-> 
    let boxed_expr = box_help_func (expr,stringList) in 
    let boxed_exprlist = (List.map box_help_func (List.map  (fun(x)->(x,stringList)) exprlist)) in 
    ApplicTP'(boxed_expr,boxed_exprlist)


|_->raise X_syntax_error;;

let annotate_lexical_addresses e = 
              let empty_lst = [] in 
              get_lexical_addresses(e,empty_lst);;

let annotate_tail_calls e = 
              work_with_applics (e,false);;
 
let box_set e = 
              let empty_lst = [] in 
              box_help_func (e,empty_lst);;
let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;;

