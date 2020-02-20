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
  (* val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string *)
    val generate : (constant * (int * 'a))     list -> (String.t * int) list -> expr' -> int -> string

end;;

module Code_Gen : CODE_GEN = struct
  (* let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;; *)

exception X_should_not_happen ;;

(******************  START WITH CONSTS TABLE  ****************)
let extract_ast_consts ast = 
  let consts_lst = ref [] in 
  let rec consts_helper e = 
  match e with 
  | Const'(sexpr0) -> 
                    consts_lst := !consts_lst@[sexpr0]
  | BoxSet'(expr_var,expr_val) ->
                    (consts_helper expr_val) 
  | If'(expr_test,expr_then,expr_else)-> 
                    let combined = [expr_test;expr_then;expr_else] in 
                    let result = (List.map consts_helper combined) in 
                   ( match result with 
                    |_->() )
  | Seq'(exprlist) -> 
                    let result = (List.map consts_helper exprlist) in 
                    (match result with 
                    |_->()) 
  | Set'(var,expr_val) -> 
                    let result = (List.map consts_helper [var;expr_val]) in
                   ( match result with 
                    |_-> () )
  | Def'(var,expr_val) -> 
                    let result = (List.map consts_helper [var;expr_val]) in 
                    (match result with 
                    |_->() )
  | Or'(exprlist) -> 
                    let result = (List.map consts_helper exprlist) in 
                    (match result with 
                    |_->()) 
  | LambdaSimple'(params,body)-> 
                    (consts_helper body)
  | LambdaOpt'(params,str,body)->
                    (consts_helper body)
  | Applic'(expr,exprlist)-> 
                    let expr_consts = (consts_helper expr) in 
                    let exprlist_consts = (List.map consts_helper exprlist) in 
                    (match (expr_consts,exprlist_consts) with 
                    |_->() )
  | ApplicTP'(expr,exprlist)->  
                    let expr_consts = (consts_helper expr) in 
                    let exprlist_consts = (List.map consts_helper exprlist) in 
                    (match (expr_consts,exprlist_consts) with 
                    |_->() )
  |_->()  in 


let outer_consts=(consts_helper ast) in 
    (match outer_consts with 
    |_-> !consts_lst) ;; 



let rec scan_lst_with_elmnt e lst filtered_lst =
 match lst with
  | [] -> List.rev filtered_lst
  | hd::tl ->
    (match (e,hd) with 
    | (_,Void)| (Void,_)->  scan_lst_with_elmnt e tl (hd::filtered_lst)
    | (Sexpr(e1),Sexpr(x1)) when sexpr_eq e1  x1 -> scan_lst_with_elmnt e tl filtered_lst
    | _-> scan_lst_with_elmnt e tl (hd::filtered_lst)) 
   ;;


(*above no relevant after moving it to the reader*)
    let cleartagRef lst=
      let listnotag=[] in
      let rec cleartag lst listnotag=(match lst with
      |[]->listnotag
      |hd::tl-> (match hd with |Sexpr(TagRef(x))->cleartag tl listnotag
                               |Sexpr(TaggedSexpr(x,y))->cleartag tl listnotag
                               |_->let listnotag=listnotag@[hd] in
                                                cleartag tl listnotag)
      ) in
      cleartag lst listnotag;;

      let rec helprecl sexpr=match sexpr with
      |TaggedSexpr(x,y)-> let fixy=helprecl y in
                          fixy
      |Pair(a,b)-> let fixa=helprecl a in
                   let fixb=helprecl b in
                   Pair(fixa,fixb)
      |_-> sexpr
      ;;


      let cleartagsexpr lst=
        let listnotag=[] in
        let rec cleartag lst listnotag=(match lst with
        |[]->listnotag
        |hd::tl-> (match hd with |Sexpr(TaggedSexpr(x,y))->let fixtags= helprecl (TaggedSexpr(x,y)) in
                                                           let listnotag=listnotag@[Sexpr(fixtags)] in
                                                            cleartag tl listnotag
                                 |Sexpr(Pair(a,b))-> let fixtags= helprecl (Pair(a,b)) in
                                                     let listnotag=listnotag@[Sexpr(fixtags)] in
                                                     cleartag tl listnotag
                                 |_->let listnotag=listnotag@[hd] in
                                                  cleartag tl listnotag)
        ) in
        cleartag lst listnotag;;   
        
      let buildTaggedlst lst=
      let listofTag=[] in
      let rec addtag lst listofTag=(match lst with
      |[]->listofTag
      |hd::tl-> (match hd with |Sexpr(TaggedSexpr(x,y))-> let fixTag= helprecl y in
                                                        let tag_add=(Sexpr(TaggedSexpr(x,fixTag)),0) in
                                                          
                                                        let listofTag=listofTag@[tag_add] in
                                                        let fixinside= addtag  [(Sexpr(y))] listofTag in
                                                        
                                                        addtag tl fixinside  
                               |Sexpr(Pair(a,b))-> let fixa= addtag [Sexpr(a)] listofTag  in
                                                   let listofTag=fixa in
                                                   let fixb=addtag [Sexpr(b)] listofTag  in
                                                   let listofTag=fixb in
                                                   addtag tl listofTag  
                               |_-> addtag tl listofTag  )
      ) in
      addtag lst listofTag;;  


      let findaddofequaltag tag cnst=
        (match tag with |(Sexpr(TaggedSexpr(x,y)),add1)->
          (match cnst with |(Sexpr(sm),(add2,string))-> if(y=sm) then true else false
                           |_->false)
                        |_-> false
        );;


      let getadressofTagged lstTag cnstable=
        let listofaddTag=[] in
        let rec make lstTag cnstable listofaddTag=
        (match lstTag with|[]->listofaddTag
                          |hd::tl-> (match hd with |(Sexpr(TaggedSexpr(x,y)),add1)->
                                                  let equal=(List.filter (findaddofequaltag (Sexpr(TaggedSexpr(x,y)),add1) ) cnstable) in
                                                  let add2= match equal with |[(Sexpr(sm),(add,string))]->add
                                                                             |_->raise X_should_not_happen in
                                                  let newtag=(Sexpr(TaggedSexpr(x,y)),add2) in
                                                                             
                                                  let listofaddTag=listofaddTag@[newtag] in
                                                  make tl cnstable listofaddTag
                                                  |_->raise X_should_not_happen)
                         )

        in
        make lstTag cnstable listofaddTag;;
     

(****************************until here tagged************************************ *)
let remove_duplications_c lst = 
let filtered_lst = [] in 
let rec loop_on_elements lst filtered_lst =
    match lst with
    | [] -> List.rev filtered_lst
    | hd :: tl -> loop_on_elements (scan_lst_with_elmnt hd tl []) (hd::filtered_lst)
in
(loop_on_elements lst filtered_lst) ;; 

 (*'#{x}=(1 #{y} 1 #{y}=(2 . #{y}) . #{x})
 [(Void,(0,"MAKE_VOID"));
 (Sexpr(Nil),(1,"MAKE_NIL"));
 (Sexpr(Bool false),(2,"MAKE_BOOL(0)"));
 (Sexpr(Bool true),(4,"MAKE_BOOL(1)"));
(Sexpr(Number(Int 1)),(6,"MAKE_LITERAL_INT(1)"));
(Sexpr(Number(Int 2)),(15,"MAKE_LITERAL_INT(2)"));
(Sexpr(Pair(Number(Int 2),TagRef "y1")),(24,"MAKE_LITERAL_PAIR(const_tbl+15, const_tbl+24)"));
(Sexpr(Pair(Pair(Number(Int 2),TagRef "y1"),TagRef "x1")),(41,"MAKE_LITERAL_PAIR(const_tbl+24, const_tbl+92)"));
(Sexpr(Pair(Number(Int 1),Pair(Pair(Number(Int 2),TagRef "y1"),TagRef "x1"))),(58,"MAKE_LITERAL_PAIR(const_tbl+6, const_tbl+41)"));
(Sexpr(Pair(TagRef "y1",Pair(Number(Int 1),Pair(Pair(Number(Int 2),TagRef "y1"),TagRef "x1")))),(75,"MAKE_LITERAL_PAIR(const_tbl+24, const_tbl+58)"));
(Sexpr(Pair(Number(Int 1),Pair(TagRef "y1",Pair(Number(Int 1),Pair(Pair(Number(Int 2),TagRef "y1"),TagRef "x1"))))),(92,"MAKE_LITERAL_PAIR(const_tbl+6, const_tbl+75)"))
];;
*)
(*nested concsts can be Pairs/symbols/vectors*)
  let rec get_sub_consts const0 =
    match const0 with
    | Sexpr(a) ->
       (match a with
        | Symbol(str_name) ->
           [Sexpr(String(str_name))] @ [const0]
        | Pair(a, b) ->
           (get_sub_consts (Sexpr a)) @
             (get_sub_consts (Sexpr b)) @ [const0]
        (*deal with tagged*)
        |TaggedSexpr(name,sexpr)-> (get_sub_consts (Sexpr sexpr)) @ [const0]
        (*deal with tagged*)
        | _ -> [const0])
    | _ -> [const0];;


(*according to trgol 9 + 10 *)
  let get_offset_toadd number  const0 =
    match  const0 with 
    | Void-> number+1
    | Sexpr(Bool(x))-> number+2
    | Sexpr(Nil)-> number+1
    | Sexpr(Number(x))-> number +9
    | Sexpr(Char(x))-> number +2
    | Sexpr (String(x))-> number+9+ (String.length x)
    | Sexpr (Symbol(x))-> number+9
    | Sexpr(Pair(car,cdr))-> number+17
    (*change for tagged*)
    |Sexpr(TagRef(name))->number+0
    |Sexpr(TaggedSexpr(name,rest))->number+0
    (*change for tagged*)

  let rec get_const_with_offset  list1 list2=
   match list1 with
   | []->list2
   | _ -> let(a,b)= (List.hd(List.rev list2)) in get_const_with_offset (List.tl list1 ) (list2@[(List.hd list1,(get_offset_toadd b a))])
;;

      
  let rec get_offset_of_const list2 sexpr1=
      match  list2 with
      | []->raise X_should_not_happen
      | _-> 
        (match sexpr1 with 
        (*the first 4 elements in the tbl are known by definition *)
        | Void -> 0
        | Sexpr(Nil) -> 1
        | Sexpr(Bool true) -> 2
        | Sexpr(Bool false) -> 4
        (******change tag***** *)
        | Sexpr(TagRef(x))-> -1
        (* | Sexpr(TagRef(x))-> raise X_should_not_happen *)
        (******change tag***** *)


        (*now we should compute the offset according to the Sexpr that we have*)
        | Sexpr(x)->  
          let (sexpr,(offset_number,label))=(List.hd list2) in
            (match sexpr with 
            |Void -> get_offset_of_const (List.tl list2) sexpr1
            | Sexpr(a)->
              let is_eq = (sexpr_eq a x) in 
              (match is_eq with 
              | true->  offset_number
              | false-> get_offset_of_const (List.tl list2) sexpr1)))
              (*********************add tagged /  pair case*******************
              look at semantic output heeeereg*)
            ;;


            
 

  let check_tagged   sexpr =
    let rec loop  e = 
    match e with 
    |TaggedSexpr(a,b)->  loop  b  
    |Pair(a,b)-> let a1 = loop  a in 
                 let b1 = loop  b in 
                 Pair(a1,b1) 
    |_-> e 
  in 
  let result = loop  sexpr  in 
        result
  ;; 



  let rec get_offset_of_const_tagg  consts_tbl   const=
 
      match  consts_tbl with
      | []->raise X_should_not_happen
      | _-> 
        (match const with 
        (*the first 4 elements in the tbl are known by definition *)
        | Void -> 0
        | Sexpr(Nil) -> 1
        | Sexpr(Bool true) -> 2
        | Sexpr(Bool false) -> 4
        (******change tag***** *)
        | Sexpr(TagRef(x))-> -1 (*(deal_with_tagref consts_tbl x)*)
        (* | Sexpr(TagRef(x))-> raise X_should_not_happen *)
        (******change tag***** *)

        (*now we should compute the offset according to the Sexpr that we have*)
        | Sexpr(x)->  
          let ex = (check_tagged  x) in 
          let (sexpr,(offset_number,label))=(List.hd consts_tbl) in
            (match sexpr with 
            |Void -> get_offset_of_const_tagg (List.tl consts_tbl) (Sexpr(ex))
            | Sexpr(a)->
              let is_eq = (sexpr_eq a x) in 
              (match is_eq with 
              | true->  offset_number
              | false-> get_offset_of_const_tagg (List.tl consts_tbl)  (Sexpr(ex))))   )
  
              (*********************add tagged /  pair case*******************
              look at semantic output heeeereg*)
            ;;

  let string_of_char_code_splitted str_name =
    let string_to_chars_lst = string_to_list str_name in
    let get_string_of_char =  (fun c->string_of_int(Char.code c)) in 
     ( String.concat "," (List.map  get_string_of_char  string_to_chars_lst))
     ;;

  let get_labels ((const0,number) ,list2)= 
      let label = 
      (match  const0 with 
      | Void->    "MAKE_VOID" 
      | Sexpr(Bool(true))->  "MAKE_BOOL(1)"
      | Sexpr(Bool(false))->  "MAKE_BOOL(0)" 
      | Sexpr(Nil)->  "MAKE_NIL" 
      | Sexpr(Number(Int(x)))->  "MAKE_LITERAL_INT("^(string_of_int(x))^")" 
      | Sexpr(Number(Float(x)))->   "MAKE_LITERAL_FLOAT("^string_of_float(x)^")" 
      | Sexpr(Char(x))->  "MAKE_LITERAL_CHAR("^(string_of_int(int_of_char x))^")" 
      | Sexpr (String(x))->  "MAKE_LITERAL_STRING "^(string_of_char_code_splitted x) 
      | Sexpr (Symbol(x))-> let number1= get_offset_of_const list2 (Sexpr (String(x))) in 
                            let s1= "const_tbl+"^string_of_int(number1) in 
                             "MAKE_LITERAL_SYMBOL("^s1^")" 

     

      | Sexpr(Pair(car,cdr))->  
        let string1= "const_tbl+"^ string_of_int(get_offset_of_const list2 (Sexpr(car))) in
        let string2= "const_tbl+"^ string_of_int(get_offset_of_const list2 (Sexpr(cdr))) in 
         "MAKE_LITERAL_PAIR("^string1^","^string2^ ")" 
      

      
      (*Edit of Jonathan for taggedSexpr*)
      |Sexpr(TaggedSexpr(name,rest))-> "its soudnt happend"
      |Sexpr(TagRef(name))->"its souldnt happen"
       (*Edit of Jonathan for taggedSexpr*)
      ) in 
      ( const0,(number,label))  
      

  ;;


let  rec get_consts_offset_label tuples_const_offset labled_tuples=
    match tuples_const_offset with 
    | []->labled_tuples
    | _-> let tl1 =(List.tl tuples_const_offset) in 
          let hd1 =(List.hd tuples_const_offset) in
          let labeled = (get_labels (hd1 ,labled_tuples)) in 
          (get_consts_offset_label tl1 (labled_tuples@[labeled]));;

let create_constant_table set = 
let tl = (List.tl set) in 
let hd = (List.hd set) in 
let first_tuple = (hd,0) in 
let tuples_const_offset = (get_const_with_offset tl [first_tuple]) in 
let labeled_tuples= (get_consts_offset_label tuples_const_offset []) in 
labeled_tuples
;;

let getaddinct consts const0  = 
  let const_int_address = (get_offset_of_const consts const0 ) in
  let str_address = (string_of_int const_int_address) in 
  "const_tbl+"^str_address;;

let addressoftag tagname listofTagswithadd= 
  let getthename s= match s with|(Sexpr(TaggedSexpr(name,v)),add)->name
                                |_->raise X_should_not_happen in
  let gettheadd s=match s with|[(Sexpr(TaggedSexpr(name,v)),add)]->add 
   |_->raise X_should_not_happen in

  let bul tagname s= if (getthename s = tagname) then true else false in 
  let equalname= (List.filter (bul tagname) listofTagswithadd) in
  let correctadress= gettheadd equalname in
  correctadress;;
   
  let fixconsttable consts_table listofTagswithadd=
    let fullct=consts_table in
    let fixC=[] in
    let rec fix fixC consts_table listofTagswithadd=
     (match consts_table with |[]->fixC
                              |hd::tl-> (match hd with 
 |(Sexpr(Pair(a,b)),(add,string))->
  (match (a,b) with |(TagRef(name1),TagRef(name2))-> let add1="const_tbl+"^(string_of_int (addressoftag name1 listofTagswithadd))in
                                                     let add2="const_tbl+"^(string_of_int(addressoftag name2 listofTagswithadd)) in
                    let fixTag= (Sexpr(Pair(a,b)),(add,"MAKE_LITERAL_PAIR("^add1^","^add2^ ")" )) in
                    let fixC= fixC@[fixTag] in
                    fix fixC tl listofTagswithadd
                    |(TagRef(name1),notagref)->let add1="const_tbl+"^(string_of_int (addressoftag name1 listofTagswithadd))in
                                               let add2=getaddinct fullct (Sexpr(notagref)) in
                                               let fixTag= (Sexpr(Pair(a,b)),(add,"MAKE_LITERAL_PAIR("^add1^","^add2^ ")" )) in  
                                               let fixC= fixC@[fixTag]  in 
                                               fix fixC tl listofTagswithadd
                    |(notagref,TagRef(name2))->let add2="const_tbl+"^(string_of_int (addressoftag name2 listofTagswithadd))in
                                               let add1=getaddinct fullct  (Sexpr(notagref)) in
                                               let fixTag= (Sexpr(Pair(a,b)),(add,"MAKE_LITERAL_PAIR("^add1^","^add2^ ")" )) in  
                                               let fixC= fixC@[fixTag] in 
                                               fix fixC tl listofTagswithadd
                    |(notagref1,notagref2)->let add1=getaddinct fullct  (Sexpr(notagref1)) in
                                            let add2=getaddinct fullct  (Sexpr(notagref2)) in
                    let fixTag= (Sexpr(Pair(a,b)),(add,"MAKE_LITERAL_PAIR("^add1^","^add2^ ")" )) in  
                    let fixC= fixC@[fixTag] in
                    fix fixC tl listofTagswithadd )

|_-> let fixC= fixC@[hd] in
fix fixC tl listofTagswithadd 
                              )
                              ) in
                              fix fixC consts_table listofTagswithadd;;

                   
                
                               

(* according to slides 32+33 chapter 6 *)
let make_consts_tbl asts =
  let outer_consts_lists = (List.map extract_ast_consts asts) in 
   let outer_consts_list = (List.flatten outer_consts_lists) in
   (****change for tagged*****)
   let listfix= outer_consts_list in
   let lisfofTags=buildTaggedlst listfix in
   let listfix2=(cleartagsexpr listfix) in
 (****change for tagged*****)
  let more_consts = [Void; Sexpr(Nil); Sexpr(Bool true); Sexpr(Bool false)] in 
  let consts_lst = more_consts@listfix2 (*outer_consts_list*) in 
  let consts_set = (remove_duplications_c consts_lst) in
  let lsts_of_expanded_set = (List.map get_sub_consts consts_set) in 
  let lst_of_expanded_set = (List.flatten lsts_of_expanded_set) in 
  let set_of_expanded_set = (remove_duplications_c lst_of_expanded_set) in 
  (****change for tagged*****)
  let lst_without_tag =cleartagRef set_of_expanded_set in
  (****change for tagged*****)
  let consts_table = (create_constant_table lst_without_tag(*set_of_expanded_set*)) in 
  let listofTagswithadd= getadressofTagged (lisfofTags) (consts_table) in
  let newconsttable= fixconsttable consts_table listofTagswithadd in
  newconsttable ;;  
(*************************   DONE WITH CONSTS TABLE  *****************************)



(*************************   START WITH FREE_VAR TABLE  *****************************)
let extract_ast_fvars ast = 
  let fvars_lst = ref [] in 
  let rec fvars_helper e = 
  match e with 
  | Const'(sexpr0) -> ()

  | Var'(VarFree v)-> fvars_lst:=!fvars_lst@[v] 
  | Var'(VarParam (v,minor))-> ()
  | Var'(VarBound (v,major,minor))->() 

  | BoxGet'(v) -> () 
  | BoxSet'(expr_var,expr_val) -> (fvars_helper expr_val)
  | If'(expr_test,expr_then,expr_else)-> 
                   let combined = [expr_test;expr_then;expr_else] in 
                   let result = (List.map fvars_helper combined) in 
                   ( match result with 
                    |_->() )
  | Seq'(exprlist) -> 
                    let result = (List.map fvars_helper exprlist) in 
                    (match result with 
                    |_->())
  | Set'(var,expr_val) -> 
                    let result = (List.map fvars_helper [var;expr_val]) in
                    ( match result with 
                    |_-> () )
  | Def'(var,expr_val) -> 
                    let result = (List.map fvars_helper [var;expr_val]) in 
                    (match result with 
                    |_->() )
  | Or'(exprlist) -> 
                    let result = (List.map fvars_helper exprlist) in 
                    (match result with 
                    |_->())
  | LambdaSimple'(params,body)-> (fvars_helper body)
                   
  | LambdaOpt'(params,str,body)->(fvars_helper body)
                  
  | Applic'(expr,exprlist)-> 
                    let expr_consts = (fvars_helper expr) in 
                    let exprlist_consts = (List.map fvars_helper exprlist) in 
                    (match (expr_consts,exprlist_consts) with 
                    |_->() )
  | ApplicTP'(expr,exprlist)->  
                    let expr_consts = (fvars_helper expr) in 
                    let exprlist_consts = (List.map fvars_helper exprlist) in 
                    (match (expr_consts,exprlist_consts) with 
                    |_->() )
  |_->()  in 
let fvars=(fvars_helper ast) in 
    (match fvars with 
    |_-> !fvars_lst) ;; 



let  remove_dup_of_element lst element  = 
  let  helper lst filtered =  
    match lst = element with 
    |true-> filtered
    |_-> lst::filtered  in 
  let init_fltered= [] in
  (List.fold_right helper lst init_fltered) ;; 

let rec remove_duplications_f lst = 
  match lst with 
  |[] -> lst 
  |_ -> let hd = (List.hd lst ) in  
       let tl = (List.tl lst ) in 
       let removed_dups_for_hd= (remove_dup_of_element tl hd ) in 
       let rest_elements_removing= (remove_duplications_f removed_dups_for_hd) in 
       [hd]@rest_elements_removing 
;;
let get_indexes_list lst_length=
  let rec get_index_helper num=
   ( match num with 
    |(-1)-> [] 
    |_-> (get_index_helper(num-1)@[num])) in
  get_index_helper (lst_length-1);;

let create_fvars_table fvars_set = 
let set_length = (List.length fvars_set) in 
let make_pairs_fun = (fun a b -> (a,b)) in 
let indexes_list = (get_indexes_list set_length) in 
List.map2 make_pairs_fun fvars_set indexes_list

;;
let make_fvars_tbl asts = 
let fvars_lsts = (List.map extract_ast_fvars asts) in 
let fvars_lst = (List.flatten fvars_lsts ) in 
let built_in_procedures = ["boolean?"; "float?" ; "integer?"; "pair?";
   "null?"; "char?"; "string?";
   "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "symbol->string"; 
   "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/" ;"<"; "="
   ;"car";"cdr";"set-car!";
    "set-cdr!";"apply"
      (* you can add yours here *)
      (* ADDED to the compiler *) 
  ; "car"; "cdr"; "set-car!"; "set-cdr!";"cons"; "apply"
              ] in 
let all_fvars = built_in_procedures @ fvars_lst in 
let fvars_set = (remove_duplications_f all_fvars) in 
let free_table = (create_fvars_table fvars_set) in 
free_table 
;;

(*************************   DONE WITH FREE VARS TABLE  *****************************)


(*************************   START WITH GENERATE  *****************************)
(*
Notes related to the function "generate" : 
1. we can make any changes in this file , as long as the makefile and other files are working . 
2. most of the implemintation if this function is according to chapter 6 slide 65 :
Code Generation▶The code generator is a function expr′->!string
We look at expr′ after the semantic analysis phase is complete
and after the constants-table and free-vars-table have been set up
The string returned is x86/64 assembly language code, line byline..
3. the sob_void / sob_nil ... are declared in the file compiler.ml as SOB_VOID_ADDRESS/SOB_NIL_ADDRESS..
*)


let rec get_offset_of_freevar list2 const=
  let (a,b)=List.hd list2 in 
  if (String.equal a const) 
  then (b) 
  else ( get_offset_of_freevar (List.tl list2) const);;


let addressInConstTable  consts   const0  = 
let const_int_address = (get_offset_of_const_tagg  consts const0 ) in
let str_address = (string_of_int const_int_address) in 
"const_tbl+"^str_address;;

let rec addressInFvarTable fvars var0 = 
let first_pair = List.hd fvars in 
let tl = (List.tl fvars) in 
match first_pair with 
|(var,index)-> if(String.equal var var0) then index else (addressInFvarTable tl var0 )
(* |_->raise X_should_not_happen  *)
;;



let rec generate consts fvars exp unique_ast_label_num = 
  let unique = 
    let last = ref 0 in fun () -> incr last ; !last in
 
  let rec generate_helper consts fvars e unique_ast_label_num ldepth= 
    match e with 

    | Const'(x)->"mov rax,"^(addressInConstTable  consts  x)^"\n"

    | Var'(v)->(match v with 
                |VarParam(x,minor)-> "mov rax,qword[rbp+8*(4+"^(string_of_int minor)^")]\n"
                |VarFree(x) ->       "mov rax, qword[fvar_tbl + WORD_SIZE*"^(string_of_int(addressInFvarTable fvars x))^"]\n"
                |VarBound(x,major,minor) -> "mov rax,qword[rbp+8*2] \n"^
                                            "mov rax,qword[rax+8*"^(string_of_int major)^"]\n"^
                                            "mov rax,qword[rax+8*"^(string_of_int minor)^"]\n"
                )
    | Box'(v) ->  (generate_helper consts fvars (Var'(v)) unique_ast_label_num ldepth)^
                    "MALLOC r8, 8 \n"^
                    "mov [r8], rax \n"^
                    "mov rax,r8 \n" 
    | BoxGet'(v) -> (generate_helper consts fvars (Var'(v)) unique_ast_label_num ldepth)^
                          "mov rax,qword[rax]\n" 
    | BoxSet'(v,expr_val) -> (generate_helper consts fvars expr_val unique_ast_label_num ldepth)^
                                    "push rax \n"^
                                    (generate_helper consts fvars (Var'(v)) unique_ast_label_num ldepth)^
                                    "pop qword [rax] \n"^
                                    "mov rax ,SOB_VOID_ADDRESS\n"



    | If'(test_e,then_e,else_e)-> let unique_num = unique() in
                                  let uni = (string_of_int unique_ast_label_num)^(string_of_int unique_num) in 
                                 (generate_helper consts fvars test_e unique_ast_label_num ldepth)^
                                  "cmp rax, SOB_FALSE_ADDRESS \n"^
                                  "je Lelse"^uni^"\n"^
                                  (generate_helper consts fvars then_e unique_ast_label_num ldepth)^
                                  "jmp Lexit"^uni^"\n"^
                                  "Lelse"^uni^":\n"^
                                  (generate_helper consts fvars else_e unique_ast_label_num ldepth)^
                                  "Lexit"^uni^":\n"

    | Seq'(exprslist)-> 
                        let generate_fun = (fun x-> generate_helper consts fvars x unique_ast_label_num ldepth) in 
                        let generated_lst = (List.map generate_fun exprslist) in 
                        let concat_fun = (fun exp1 exp2 -> exp1^exp2) in 
                        let all_in_one_string=List.fold_left concat_fun "" generated_lst  
                        in all_in_one_string 


    | Set'(Var'(v),expr_val)->( match v with 
                      |VarParam(x,minor)->     (generate_helper consts fvars expr_val unique_ast_label_num ldepth)^
                                               "mov qword[rbp+8*(4+"^(string_of_int minor)^")],rax \n"^
                                               "mov rax, SOB_VOID_ADDRESS\n"
                      |VarBound(x,major,minor)-> (generate_helper consts fvars expr_val unique_ast_label_num ldepth)^
                                                "mov rbx, qword[rbp+8*2] \n"^
                                                "mov rbx, qword[rbx+8*"^(string_of_int major)^"] \n"^
                                                "mov qword[rbx+8*"^(string_of_int minor)^"], rax \n"^
                                                "mov rax, SOB_VOID_ADDRESS\n"
                      |VarFree(x)->             (generate_helper consts fvars expr_val unique_ast_label_num ldepth)^
                                                 "mov qword[fvar_tbl + WORD_SIZE*"^(string_of_int(addressInFvarTable fvars x))^"], rax \n"^
                                                 "mov rax, SOB_VOID_ADDRESS \n")



    | Def'(Var'(VarFree(v)),expr_val) ->(generate_helper consts fvars expr_val unique_ast_label_num ldepth)^
                                        "mov qword[fvar_tbl + WORD_SIZE*"^(string_of_int(addressInFvarTable fvars v))^"], rax \n"^
                                        "mov rax,SOB_VOID_ADDRESS \n "

    | Or'(exprslist) -> let gen= (fun x-> generate_helper consts fvars x unique_ast_label_num ldepth) in 
                        let generated_lst = (List.map gen exprslist) in  
                        let unique_num = unique() in
                        let uni = (string_of_int  unique_ast_label_num)^(string_of_int unique_num) in 
                        let rec or_helper lst  = 
                        (match lst with 
                        |[]->""
                        |[one_element] -> one_element^"Lexit"^uni^":\n"
                        |hd::tl -> (hd^"cmp rax, SOB_FALSE_ADDRESS
                                                   jne Lexit"^uni^"\n" )^(or_helper tl ) )
                        in (or_helper generated_lst) 

    | Def'(exprvar,exprval)->(
        match exprvar with
        | Var'(VarFree(s))-> 
            let converted = (Set'(exprvar,exprval)) in 
            (generate_helper consts fvars converted unique_ast_label_num ldepth)
        | _->raise X_this_should_not_happen
        )



    | Applic'(proc,exprlist)->( 
        let str_length = (string_of_int((List.length exprlist))) in
        let gen_add_str = (fun x->(generate_helper consts fvars x unique_ast_label_num ldepth)^ "push rax\n") in
        let revlst = (List.rev exprlist) in 
        let exprlist=(List.map gen_add_str revlst) in
        let concat = (fun x y-> x^y) in 
        let exprs_lst_final = (List.fold_left concat "" exprlist) in 
        exprs_lst_final^
        "push "^str_length^"\n"^
        (generate_helper consts fvars proc unique_ast_label_num ldepth)^"\n"^ 
        "CLOSURE_ENV rbx ,rax\n"^
        "push rbx\n"^
        "CLOSURE_CODE rcx ,rax\n"^
        "call rcx\n"^
        "add rsp , 8*1\n"^
        "pop rbx\n"^
        "shl rbx , 3\n"^
        "add rsp , rbx\n"  
       )


    | ApplicTP'(proc,exprlist)-> (
        let str_length = (string_of_int((List.length exprlist))) in
        let gen_add_str = (fun x->(generate_helper consts fvars x unique_ast_label_num ldepth)^ "push rax\n") in
        let revlst = (List.rev exprlist) in 
        let generated_exprlist=(List.map gen_add_str revlst) in
        let concat = (fun x y-> x^y) in 
        let exprs_lst_final = (List.fold_left concat "" generated_exprlist) in
        exprs_lst_final^
        "push "^str_length^"\n"^
        (generate_helper consts fvars proc unique_ast_label_num ldepth)^"\n"^ 
        "CLOSURE_ENV rbx ,rax\n"^
        "push rbx\n"^
        "CLOSURE_CODE rcx ,rax\n"^
        "push qword[rbp+8*1]"^"\n"^
        "mov rax,qword[rbp]"^"\n"^
        "SHIFT_FRAME("^(string_of_int((List.length exprlist)+4))^")\n"^ (*+3 = proc+env+old rbp*)
        "mov rbp,rax\n"^
        "jmp rcx\n"
        )



  
  
    | LambdaSimple'(stringlist,body)->  
      let number=unique() in
      let uni = (string_of_int unique_ast_label_num)^(string_of_int number) in 
      let generated_body = (generate_helper consts fvars body unique_ast_label_num (ldepth+1)) in 
      let lcode=  "MAKE_CLOSURE(rax, r15, Lcode"^uni ^")\n"^
                  "jmp Lcont"^uni ^"\n\n"^

                  "Lcode"^uni ^":\n"^
                  "push rbp\n"^
                  "mov rbp,rsp\n"^
                  generated_body^
                  "leave\n"^
                  "ret\n\n"^

                  "Lcont"^uni ^":\n" in 
        ( match ldepth with 
          | 0->
          (*  allocate closure object : closure env  = Nil ,closure code = Lcode*)
            "mov r15,SOB_NIL_ADDRESS\n"^ (*copy env=nil to r15*)
             lcode

          |_ ->
            let allocating_new_env = (*allocating the ExtEnv => |ExtEnv| = (1+ |Env|)*8 each cell in the stack  *)
                      "MALLOC rbx, "^(string_of_int((ldepth+1)*8))^"\n"^
                      "mov r14,rbx\n"^
                      "mov r8, qword[rbp+8*2]"^"\n"^                                 (* r8 = old env *)
                      "mov rcx,"^(string_of_int(ldepth))^"\n"^  
                      "mov r9,rcx\n\n" in                                             (* r9 = |old env|*)
            let copy_minors_toNewEnv =  (*copiy pointers of minor vectors from Env to Extenv*)
                      "Copy_Env_to_ExtEnv"^uni ^":"^"\n"^
                      "mov r10,qword[r8+rcx*8-8]\n"^
                      "mov qword[r14+r9*8],r10\n"^
                      "dec r9\n"^
                      "loop Copy_Env_to_ExtEnv"^uni ^", rcx\n\n" in                (* rcx is decremented automatically by loop*)
            let allocating_for_params = (*allocate ExtEnv[0] = parameters of the old Env*)
                      "mov rax,qword[rbp+3*8]"^"\n"^                                (* rax = n *)
                      "shl rax,3 \n"^                                               (* rax = 8*n *)
                      "MALLOC rax,rax\n"^                                           
                      "mov r11,rax \n"^                                             (* r11 =points to free space of size 8*n *)
                      "mov r10,4\n"^                                                (* for iter on the old mem args *) 
                      "mov r12,0\n\n"^                                              (* for iter on new allocated mem - r11 *)
                      "mov rcx,qword[rbp+3*8]\n"^                                   (* rcx = n *)
                      "cmp rcx,0"^"\n"^
                      "je zero_params"^uni ^"\n" in 
          let copy_params_to_new_env= (* copy the params of the old env in ExtEnv[0]*)
                      "copy_old_params"^uni ^":\n"^
                      "mov r9,qword[rbp+r10*8]\n"^                                 (* r9 = arg0*)
                      "mov qword[r11+r12*8],r9\n"^                                 (* r11[0] = arg 0 *)
                      "add r12,1\n"^ 
                      "add r10,1\n"^
                      "loop copy_old_params"^uni ^",rcx\n\n"^
                      "zero_params"^uni ^":\n"^
                      "mov qword[r14],r11\n" in                                        (*put the new allocated mem of the params
                                                                        intto the new ExtEnv[0]-rbx[0]=rbx  *)
          let generated_lambda = 
            allocating_new_env^
            copy_minors_toNewEnv^
            allocating_for_params^
            copy_params_to_new_env^
            "mov r15,rbx\n"^    (*copy env into r15*)
            lcode in 
            generated_lambda 
     )
  
  
    
  
    | LambdaOpt'(stringlist,stringopt,body)->(  
      let number=unique() in
         let uni = (string_of_int unique_ast_label_num)^(string_of_int number) in 
      let generated_body= (generate_helper consts fvars body unique_ast_label_num (ldepth+1)) in 
      let str_length = (string_of_int (List.length stringlist)) in 
      let make_pair =(*make list - nested pairs - of the opt args*)
                  "make_pair"^uni^":"^"\n"^
                  "mov r10, qword[r8]"^"\n"^
                  "MAKE_PAIR(r15,r10,r12)"^"\n"^
                  "mov r12,r15"^"\n"^
                  "sub r8, 8"^"\n"^
                  "loop make_pair"^uni ^", rcx"^"\n\n" in 
      let shift_down_frame = 
                  "shift_frame"^uni ^":"^"\n"^
                  "mov r14,qword[r12]"^"\n"^
                  "sub r12,8"^"\n"^
                  "mov qword[r12],r14"^"\n"^
                  "add r12,8*2"^"\n"^
                  "loop shift_frame"^uni^",rcx"^"\n\n" in 
      let lcode1 = "MAKE_CLOSURE(rax, r15, Lcode"^uni ^")\n"^
                  "jmp Lcont"^uni ^"\n\n"^

                  "Lcode"^uni ^":\n"^
                  "push rbp\n"^
                  "mov rbp,rsp\n"^
                  
                  "mov r8,[rbp+3*8]"^"\n"^ (* r8 = n *)
                  "cmp r8,"^str_length^"\n"^
                  "je add_empty_list"^uni ^"\n\n"^

                  "put_args_in_list"^uni ^":"^"\n"^ 
                  "mov r9,"^str_length^"\n"^
                  "sub r8,r9"^"\n"^ (*r8 = n - |stringlst| = |opt|*)
                  "mov rcx,r8"^"\n"^ (*rcx = |opt|*)
                  "dec rcx"^"\n"^
                  "mov r8,[rbp+3*8]"^"\n"^ (*r8 = n *)
                  "add r8,3"^"\n"^ (* r8 = n +3  (ret + env +old rbp) *)
                  "shl r8,3"^"\n"^ (*r8 = n+3 * 8*)
                  "add r8,rbp"^"\n"^ (*r8 = rbp + 3+n *8 => r8 all the new size needed*)
                  "mov r10, qword[r8]"^"\n"^ (*r10 = arg n-1 *)
                  "MAKE_PAIR(r15,r10,SOB_NIL_ADDRESS)"^"\n"^ 
                  "mov r12,r15"^"\n"^
                  "sub r8, 8"^"\n"^
                  "cmp rcx, 0"^"\n"^
                  "je cont"^uni^"\n\n" in 
          let lcode2 = "cont"^uni^":\n"^
                  "add r8, 8"^"\n"^
                  "mov qword[r8],r12"^"\n"^
                  "jmp move_on"^uni ^"\n\n"^
                  "add_empty_list"^uni ^":"^"\n"^
                  "mov qword[rbp+3*8],"^(string_of_int((List.length stringlist)+1))^"\n"^
                  "sub rbp,8"^"\n"^
                  "mov rcx,"^(string_of_int((List.length stringlist)+4))^"\n"^
                  "mov r12,rbp"^"\n"^
                  "add r12,8"^"\n\n"^
                  shift_down_frame^
                  "sub r12,8"^"\n" in 

      match ldepth with 
        | 0->(
                "mov r15,SOB_NIL_ADDRESS \n"^
                lcode1^
                make_pair^
                lcode2 ^
                "mov r9, SOB_NIL_ADDRESS "^"\n"^
                "mov qword[r12],r9"^"\n"^ 
                "move_on"^uni ^":"^"\n"^
                generated_body^
                "leave\n"^
                "ret\n\n"^
                "Lcont"^uni ^":\n"
        )
        |_->(
          let allocating_new_env = 
                  "MALLOC rbx, "^(string_of_int((ldepth+1)*8))^"\n"^
                  ";mov r14,rbx \n"^
                  "mov r8, qword[rbp+8*2]"^"\n"^
                  "mov rcx,"^(string_of_int(ldepth))^"\n"^  
                  "mov r9,rcx\n\n" in
          let copy_minors_toNewEnv =
                  "Copy_Env_to_ExtEnv"^uni ^":"^"\n"^
                  "mov r10,qword[r8+rcx*8-8]\n"^
                  "mov qword[rbx+r9*8],r10\n"^
                  "dec r9\n"^
                  "loop Copy_Env_to_ExtEnv"^uni ^", rcx\n\n" in  
          let allocating_for_params = 
                  "mov rax,qword[rbp+3*8]"^"\n"^
                  "shl rax,3 \n"^
                  "MALLOC rax,rax\n"^
                  "mov r11,rax \n"^
                  "mov r10,4\n"^
                  "mov r12,0\n\n"^
                  "mov rcx,qword[rbp+3*8]\n"^
                  "cmp rcx,0"^"\n"^
                  "je zero_params"^uni ^"\n" in 
          let copy_params_to_new_env= 
                  "copy_old_params"^uni ^":\n"^
                  "mov r9,qword[rbp+r10*8]\n"^
                  "mov qword[r11+r12*8],r9\n"^
                  "add r12,1\n"^ 
                  "add r10,1\n"^
                  "loop copy_old_params"^uni ^",rcx\n\n"^
                  "zero_params"^uni ^":\n"^
                  "mov qword[rbx],r11\n" in 
          
          let lcode = 
                  "mov r15,rbx \n"^
                  lcode1^
                  make_pair^
                  lcode2^
                  "sub rsp,8"^"\n"^
                  "mov r9, SOB_NIL_ADDRESS "^"\n"^
                  "mov qword[r12],r9"^"\n"^
                  "move_on"^uni ^":"^"\n"^
                  generated_body^
                  "leave\n"^
                  "ret\n\n"^
                  "Lcont"^uni ^":\n" in 

          let generated_lambda = 
              allocating_new_env^
              copy_minors_toNewEnv^
              allocating_for_params^
              copy_params_to_new_env^
              lcode 
          in generated_lambda 
        )
    )

    

    |_->"" 
  in (generate_helper consts fvars exp unique_ast_label_num 0);;
  


end;; 