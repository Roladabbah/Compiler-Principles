#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception X_this_should_not_happen1;;
exception X_this_should_not_happen2;;


type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;




let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;
  
module Reader : sig


  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list

end
= struct


let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

  (* let read_sexpr string = raise X_not_yet_implemented ;;

let read_sexprs string = raise X_not_yet_implemented;;

end;;      *)
(*return to the end of the file before submit*)



(************************** Add Code Here!  **************************)

 let nt_whitespace1=  pack  (nt_whitespace) (fun  a->[] );;
 let nt_something = (range (char_of_int 11)(char_of_int 127));;
 let nt_LineComment1 =
(pack (caten (caten (char ';')(star nt_something))(disj(char '\n') (pack nt_end_of_input (fun _ -> '\n'))))
(fun((a,b),c)->[])) ;;
(********* whitespace , comments  ***********)
let nt_whiteSpaces =(pack (star nt_whitespace) (fun(a)->[]));;

let nt_LineComment =
(pack (caten (caten (char ';')(star nt_something))(disj(char '\n') (pack nt_end_of_input (fun _ -> '\n'))))
(fun((a,b),c)->' ')) ;;



let nt_boolean =(disj (pack(caten(char '#')(char_ci 't'))
(fun (solamet,tr)-> Bool(true)))
(pack(caten(char '#')(char_ci 'f'))
(fun (solamet,fl)-> Bool(false))))
;;


(********* Char  ***********)


let nt_namedChar =disj_list [
    pack (word_ci "nul")     (fun (a)     -> (char_of_int 0))
  ; pack (word_ci "newline") (fun (a) -> (char_of_int 10))
  ; pack (word_ci "return")  (fun (a)  -> (char_of_int 13))
  ; pack (word_ci "tab")     (fun (a)     -> (char_of_int 9))
  ; pack (word_ci "page")    (fun (a)    -> (char_of_int 12))
  ; pack (word_ci "space")   (fun (a)   -> (char_of_int 32))] ;;

let nt_charPrefix = (word_ci "#\\");;
let nt_visibleSimpleChar = (range (char_of_int 33) (char_of_int 126));;
let nt_char =(pack (pack (pack (caten nt_charPrefix (disj_list [nt_namedChar; nt_visibleSimpleChar;]))  
  (fun(h,t)-> h@[t]))(fun (ls)->(List.hd(List.tl(List.tl ls)))))(fun(a)-> Char(a)));;

(********* Number  ***********)

let nt_digit= (range '0' '9');;
let nt_natural = let plus_digit_ls =  (plus nt_digit) in 
    let str_digits= (pack plus_digit_ls (fun(ls)->(list_to_string ls))) in (pack str_digits (fun(s)->(int_of_string s)));;


 let nt_integer_withplus = (pack(caten(disj (char '+')(char '-'))nt_natural) 
  (fun(minus_plus,num)->match minus_plus with 
  | '+' -> num
  | '-' -> (~-)num
  | _-> raise X_this_should_not_happen));;

let nt_integer_withoutplus =(pack  nt_natural(fun(num)-> num));;

let nt_integer = (disj nt_integer_withoutplus nt_integer_withplus);;

let nt_float1= (pack(pack(caten (pack(pack (caten nt_integer (char '.')) (fun(a,b)->a))
(fun(a)-> string_of_int a))(pack (plus nt_digit) (fun(ls)-> (list_to_string ls))))
(fun(a,b)-> (a^"."^b)))(fun (str_num)->(float_of_string str_num)));; 
 
let nt_int_for_nt_float=    
  (pack (caten (disj (char '+')(char '-')) nt_natural) 
  (fun(minus_plus,num)->match( minus_plus,num) with 
  | ('+',num) -> (string_of_int num)
  | ('-',0) -> "-"^(string_of_int num) 
  | ('-',num) -> (string_of_int ((~-)num))
  | _-> raise X_this_should_not_happen));;

let nt_float= (disj (pack (pack(caten (pack (caten nt_int_for_nt_float (char '.')) 
(fun(a,b)->a))(pack (plus nt_digit) (fun(ls)-> (list_to_string ls))))
(fun(a,b)->  (a^"."^b) ))(fun (str_num)-> float_of_string str_num)) nt_float1 )
;; 

(******** Scientific notation**********)

let nt_scientific =  (pack (disj(pack (caten(pack(caten nt_integer (char_ci 'e'))
(fun(a,b)->a))nt_integer)(fun(a,b)-> 10.0**(float_of_int b)*.(float_of_int a))) 
(pack (caten(pack(caten nt_float (char_ci 'e'))(fun(a,b)->a))nt_integer)
(fun(a,b)-> 10.0**(float_of_int b)*.a)))(fun(a)->Number (Float a))) 
;; 

(******** Radix notation**********)
let nt_capital= (pack (range (char_of_int 65)(char_of_int 90)) (fun(ch)->((int_of_char ch)-55)));; 
let nt_small = (pack (range (char_of_int 97)(char_of_int 122)) (fun(ch)->((int_of_char ch)-87))) ;; 
let nt_number09=(pack (range (char_of_int 48)(char_of_int 57)) (fun(ch)->((int_of_char ch)-48)));; 
let nt_combined = (disj_list [nt_small;nt_capital;nt_number09]);;
let nt_r=(disj (char 'r')(char 'R'));;
let nt_radix_prefix = (pack (caten (caten (char '#') nt_integer) nt_r )(fun((a,b),c)->b));;

let rec iter_radix1_ bais lst num = match num with 
| 0 -> ((float_of_int bais)**(float_of_int num))*.(float_of_int (List.hd lst))
|_ ->((float_of_int bais)**(float_of_int num))*.(float_of_int (List.hd lst))+.(iter_radix1_ bais (List.tl lst) (num-1)) 

and iter_radix2_ bais lst num = match num with 
| -1 -> ((float_of_int bais)**(float_of_int num))*.(float_of_int (List.hd lst))
| _ ->((float_of_int bais)**(float_of_int num))*.(float_of_int (List.hd lst))+.(iter_radix2_ bais (List.tl lst) (num+1)) 


and nt_radix_noSign s = 
let _radix_iter_ bais num_lst digits = (iter_radix1_ bais num_lst digits) in 
let _packed_ =
(pack
(caten nt_radix_prefix 
(pack (star nt_combined) (fun(ls)-> ls,(List.length ls)-1) ))
(fun(a,(b,c))-> (_radix_iter_ a b c)))
in _packed_ s 

and nt_radix_withSign s= 
let _radix_iter_ bais num_lst digits = (iter_radix1_ bais num_lst digits) in 
let _packed_ =
(pack
(caten (caten nt_radix_prefix (disj (char '+')(char '-')))
(pack (star nt_combined) (fun(ls)-> ls,(List.length ls)-1) ))
(fun ((bais, sign), (lst , len))-> match sign with 
| '-' -> (~-.)(_radix_iter_ bais lst len)
| '+' ->  (_radix_iter_ bais lst len)
|_-> raise X_this_should_not_happen )) 
in _packed_ s 


and nt_radix_float_noSign_ s = 
let _radix_iter1_ bais num_lst digits = (iter_radix1_ bais num_lst digits) in 
let _radix_iter2_ bais num_lst digits = (iter_radix2_ bais num_lst digits) in 
let _packed_ =
(pack
(caten
(caten
(caten nt_radix_prefix 
(pack (star nt_combined) (fun(ls)-> ls,(List.length ls)-1) ))
 (char '.'))
 (pack (star nt_combined) (fun(ls)-> List.rev ls,(~-)(List.length ls)) )) 
 (fun (((bais, (lst1, len1)), dot), (lst2, len2))-> 
 (_radix_iter1_ bais lst1 len1)+.(_radix_iter2_ bais lst2 len2)
 ))
 in _packed_ s
 

 
and nt_radix_float_withSign_  s= 
let _radix_iter1_ bais num_lst digits = (iter_radix1_ bais num_lst digits) in 
let _radix_iter2_ bais num_lst digits = (iter_radix2_ bais num_lst digits) in 
let _packed_ =
(pack
(caten
(caten 
(caten (caten nt_radix_prefix (disj (char '+')(char '-')))
(pack (star nt_combined) (fun(ls)-> ls,(List.length ls)-1) ))
(char '.'))
(pack (star nt_combined) (fun(ls)-> List.rev ls,(~-)(List.length ls)) ))
(fun ((((bais, sign), (lst1, len1)), dot), (lst2, len2)) -> match sign with 
|'+'-> (_radix_iter1_ bais lst1 len1)+.(_radix_iter2_ bais lst2 len2)
|'-' -> (~-.)((_radix_iter1_ bais lst1 len1)+.(_radix_iter2_ bais lst2 len2))
|_-> raise X_this_should_not_happen))
 in _packed_ s


 and nt_radix_ s=
 let _packed_ = 
 (disj_list [
   (pack nt_radix_float_noSign_ (fun(f_num)-> Number (Float f_num)));
   (pack nt_radix_float_withSign_ (fun(f_num)-> Number (Float f_num)));
   (pack nt_radix_withSign (fun(f_num)-> Number (Int (int_of_float f_num))));
   (pack nt_radix_noSign (fun(f_num)-> Number (Int (int_of_float f_num))));])
 in _packed_ s
;;


(********* String  ***********)

let nt_StringMetaChar =  
 (disj_list [ 
   (pack (caten (char '\\')(char '\\')) (fun( a,b ) -> '\\'));
   (pack (caten (char '\\')(char '\"')) (fun( a,b ) -> '\"'));
   (pack (caten (char '\\')(char 'f'))(fun( a,b ) -> '\012'));
  (pack (caten (char '\\') (char 't'))(fun( a,b ) -> '\t'));
  (pack (caten (char '\\') (char 'n'))(fun( a,b ) -> '\n'));
  (*addition for \n by jonathan*)
  (pack (caten (char '\\') (char 'r'))(fun( a,b ) -> '\r'));])
;;


let nt_StringLiteralChar= disj_list [
    (range (char_of_int 10)(char_of_int 33));
    (range (char_of_int 35)(char_of_int 91));
    (range (char_of_int 93)(char_of_int 127)) ];;

let nt_SymbolChar= disj_list [
    (range (char_of_int 47)(char_of_int 58));
    (range (char_of_int 65)(char_of_int 90));
    (range (char_of_int 97)(char_of_int 122));
    (char '!'); (char '$');(char '^');(char '*');
    (char '-');(char '_');(char '='); (char '+');
    (char '<');(char '>');(char '?');(char ':');];;

let nt_Symbol = 
  let ls = (plus nt_SymbolChar) in 
  let str_symbol = (pack ls (fun(lst)-> (list_to_string lst))) in 
  (pack str_symbol (fun(str)->Symbol((String.lowercase_ascii str))));;



(****nt_Number used symbol ***)
  let nt_number = (not_followed_by (disj_list[
 (pack nt_float (fun(a)-> Number(Float(a))));
 (pack nt_integer (fun(a)-> Number(Int(a))));
  ])
 nt_Symbol);;

let nt_StringChar =(disj nt_StringLiteralChar nt_StringMetaChar) ;; 

let nt_String =(pack (caten (pack (caten (char '\"')(star nt_StringChar)) (fun(a,b)->b)) 
(char '\"')) 
 (fun(lst,slash)-> String((list_to_string lst )))) ;; 



(********* some declerations to use ***********)
let nt_left_paren = (char '(');;
let nt_right_paren = (char ')');;

let tag_prefix = 
(pack 
(pack
(caten (caten (word "#{") nt_Symbol) (char '}')) 
(fun((a,b),c)->b))
(fun(a)-> match a with 
|Symbol x -> TagRef x 
|_-> raise X_this_should_not_happen))

let tag_ref=
  (pack(pack(caten(pack (caten (pack (caten (char '#')(char '{')) (fun(a,b)-> b))(nt_Symbol))
  (fun(a,b)-> b))(char '}'))(fun(a,b)-> a))
  (fun(a)-> match a with
  |Symbol a-> TagRef a
  |_-> raise X_this_should_not_happen ));;

let rec checkDuplicate tag list= 
  match tag, list with
  |TagRef(ref1) , Nil-> true 
  |TagRef(ref1), Pair(a,b)-> (checkDuplicate tag a )&&(checkDuplicate tag b)
  |TagRef(ref1), TaggedSexpr(ref2,rest)-> if(ref1=ref2) then false else (checkDuplicate tag rest)(* if the first include in the list*)
  |TagRef(ref1) , someS -> true
  |_->true
  ;;
(*
let rec inc_lude tag1 lst =
  match tag1,lst with
  | TagRef(name1), Nil-> true
  (* | TagRef(name1),TagRef(name2) ->if (name1=name2) then false else true *)
  | TagRef(name1),TaggedSexpr(name2,something) ->if (name1=name2) then false else (inc_lude tag1 something  )
  | TagRef(name1), Pair(TagRef(name2),b)->(inc_lude tag1 b  )
  | TagRef(name1), Pair(TaggedSexpr(name2,something),b)->if (name1=name2) then false else (inc_lude tag1 something)&&(inc_lude tag1 b  )
  | TagRef(name1), Pair(a,b)->(inc_lude tag1 a)&&(inc_lude tag1 b) 

  (* | TagRef(name1), [hd]@[tl] -> (inc_lude tag1 hd)&& (inc_lude tag1 [tl]) *)
  | TagRef(name1), some_sexpr -> true
  |  _ -> true;;
  *)


(******************list ****************)
let rec  _list_  s= 
let _packed_  = 

(pack
(pack (caten (caten (char '(') (star _Sexpr_) ) (char ')'))
(fun((a,b),c)-> b))
(fun(ls)-> List.fold_right 
(fun a b-> Pair(a,b))
 ls Nil))
in _packed_ s


and _DottedList_ s = 
let _packed_ = 
(pack
(caten
(caten
(pack
(caten
(pack
(caten nt_left_paren (plus _Sexpr_))
(fun(a,b)->b))
(char '.'))
(fun(a,b)->a))
_Sexpr_) nt_right_paren)
(fun((a, b), c)-> List.fold_right (fun a b -> Pair(a,b)) a b))
in _packed_ s



(********* Quote forms  ***********)
and _Quoted_ s = 
let _packed_ = 
(pack 
(pack (caten (char '\'') _Sexpr_ )(fun(a,b)->b))
(fun(sepx)->Pair(Symbol("quote"), Pair(sepx, Nil)))) in _packed_ s



and _QuasiQuoted_ s =
let _packed_ = (pack 
(pack (caten (char '`') _Sexpr_ )(fun(a,b)->b))
(fun(sexp)->Pair(Symbol("quasiquote"), Pair(sexp, Nil)))) 
in _packed_ s 

and _UnquotedSplcied_ s = 
let _packed_ = 
(pack
(pack (caten (caten (char ',')(char '@')) _Sexpr_)
(fun((a,b),c)->c))
(fun(sexp)->Pair(Symbol("unquote-splicing"), Pair(sexp, Nil))))
in _packed_ s 


and _Unquoted_ s = 
let _packed_ =
(pack 
(pack (caten (char ',') _Sexpr_ )(fun(a,b)->b))
(fun(sexp)->Pair(Symbol("unquote"), Pair(sexp, Nil))))  
in _packed_ s 

(***********Taaged Expression************)
(*
and _tagNoRef_ s = 
let _packed_ =
(pack 
(caten
(pack
(caten tag_prefix (word "=")) 
(fun(a,b)-> a))
 (  _Sexpr_))
  (fun(a,b)->match (a,b) with 
| (TagRef x,y)-> if (inc_lude a y)
then  TaggedSexpr (x,y) 
else raise X_this_should_not_happen
|_-> raise X_this_should_not_happen)
)  
in _packed_ s 
*)

and _tag1_ s=
  let packed=
    (pack(caten(pack(caten (tag_ref)(char '='))(fun(tag,eq)->tag))
      (maybe _Sexpr_))
      (fun(tag,list)-> match tag, list with
      |(TagRef x, Some (rest))-> if(checkDuplicate (TagRef x) (rest)) then TaggedSexpr (x,rest) else raise X_this_should_not_happen
      |_->raise X_this_should_not_happen)) in
   packed s 
(*
and _tagRef_ s = 
let _packed_ =
(pack

(pack
(caten
(caten
(pack
(caten
(caten 
(caten
(pack 
(caten tag_prefix (word "=(")) 
(fun(a,b)->a))
(star _Sexpr_))
(char '.'))
(star nt_whitespace))
(fun (((tag1, lst), dot), spaces)->((tag1, lst), dot)))
tag_prefix)
(char ')'))
(fun((((tag1, lst), dot), tag2),rightparen)->(((tag1, lst), dot), tag2)))
(fun(((tag1, lst), dot), tag2)-> match tag1,tag2 with 
|TagRef x ,TagRef y -> 
              (if x=y then
              let nested = (List.fold_right (fun a b -> Pair(a,b)) lst tag2) in 
               TaggedSexpr (x,nested)
               else raise X_this_should_not_happen)
|_-> raise X_this_should_not_happen ))
in _packed_ s 
*)

and iter input num=  match num with 
| 0 -> ([],input)
|_-> let (exp,rest)= ( _Sexpr_ input) in 
(iter rest (num-1))


and  _Sexprcomment_ s = 
let nt_solamet= (char '#') in
let nt_dottedcoma = (char ';') in 
let nt_solametWithoutComa= (pack (caten nt_solamet nt_dottedcoma) (fun (a,b)->a))  in
let _reiter_ (cnum,charls) =(iter charls cnum) in
_reiter_ ((pack (plus (caten nt_solametWithoutComa (star (disj_list
 [nt_whitespace1;nt_LineComment1;_Sexprcomment_]))))
(fun ls->List.length ls)) s)

and nt_nil s = 
let trash = (star  ( disj_list[nt_LineComment1;nt_whitespace1;_Sexprcomment_] ) ) in 
let packed=
((pack (caten (caten (char '(') (trash) ) (char ')'))
(fun((a,b),c)-> Nil))) in
packed s 



and  _Sexpr_ s = 

let trash = disj_list[nt_LineComment1;_Sexprcomment_;nt_whitespace1] in 
let _packed_ =
(pack (caten
(pack (caten (star trash)
(disj_list[
  nt_char;
  nt_boolean;
  nt_scientific;
  nt_radix_;
  nt_number;
  nt_Symbol;
  nt_String;
  nt_nil;
  _list_;
  _DottedList_; 
  _tag1_;
  _UnquotedSplcied_;_Unquoted_;_QuasiQuoted_; _Quoted_;
  tag_prefix;
])) (fun(a,b)->b))
(star  trash))(fun(a,b)->a))
in _packed_ s;; 


 let rec reading_str  rest_input readed=
let (expr,rest_input) = (_Sexpr_ rest_input)in
match (List.length rest_input) with 
| 0 -> (readed@[expr])
| _ -> (reading_str rest_input (readed@[expr]))
(*
Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;*)

  let inList a l = List.mem a l;;


let rec checkD sexpr refLst flag=
  
  let flagcheck sexpr refLst flag =
    match sexpr with 
    |TaggedSexpr(ref1,rest)-> (if (inList ref1 !refLst) then (flag:=1;flag)
    else  (flag:=!flag;flag))
    |_-> (flag:=!flag;flag) in

  let flagac= (flagcheck sexpr refLst flag) in
let makeList sexpr refLst flag =
  match sexpr with 
  |TaggedSexpr(ref1,rest)-> (if (inList ref1 !refLst) then (refLst:=!refLst;refLst)
  else  (refLst:=ref1::!refLst;refLst))
  |_-> (refLst:=!refLst;refLst) in

let listac=(makeList sexpr refLst flag) in


  match sexpr with
  |Pair(a,b)->(checkD a listac flagac)&&(checkD b listac flagac)
  |TaggedSexpr(ref1,rest)-> if(!flagac=1) then false else (checkD rest listac flagac)
  |_->true
  ;;

  let makeEmptyList s1 = 
    let remptylist = ref [] in 
    let flag = ref 0 in
    (checkD s1 remptylist flag);;

(************************************fix tagged list for code-gen********************************)
let bldlst a= [a];; 
let removelst a = match a with |[]-> Nil
|hd::tl-> hd;;
let bld_lst_frm_pair pair= match pair with |Pair(a,b)-> [a;b]
|Nil->[]
|_->raise X_this_should_not_happen;;
let bld_pair_frm_lst lst= match lst with
|[]->Nil
|[a ; b]-> (Pair(a,b))
|_->raise X_this_should_not_happen;;

let counter = ref 1;;
let build_lst_names lst=
  let nameref_lst= ref [] in
  let rec nameslist lst namesref= 
    (match lst with
    |[]->namesref
    |hd::tl-> (match hd with |TaggedSexpr(name,expr)-> if(List.mem name !namesref) 
                            then (
                              let lstofexpr=bldlst expr in
                              let nameref=(nameslist lstofexpr namesref) in
                              (*(nameslist lstofexpr namesref);nameslist tl namesref) *)
                              nameslist tl nameref)
                            else (namesref:=name::!namesref;
                            let nameref=(nameslist [expr] namesref) in(*(nameslist [expr] namesref)*) (nameslist tl nameref))
                           
                            |Pair(a,b)-> let lstofexpr=bld_lst_frm_pair (Pair(a,b)) in
                            (nameslist lstofexpr namesref)
                            |_->(nameslist tl namesref))
    (*| TaggedSexpr(name,expr)-> if(List.mem name !namesref) 
    then namesref else (namesref:=name::!namesref;namesref)*)
    ) in
   nameslist lst nameref_lst;;
  let rec insidefix exp lstoftags=
    match exp with 
                   |TagRef(name)->if(List.mem name !lstoftags)
                   then (let pre var= if(var=name) then true else false in
                         let numofTag= (List.length(List.filter pre !lstoftags)) in
                         let fixnum= if(numofTag==1) then 1 else (numofTag-1) in                        
                         let newname=name^(string_of_int fixnum) in                                  
                         let tagnew =TagRef newname in
                         tagnew)                       
                         else  (let pre var= if(var=name) then true else false in
                         let numofTag= (List.length(List.filter pre !lstoftags)) in
                         let fixnum= if(numofTag==1) then 1 else (numofTag-1) in                        
                         let newname=name^(string_of_int fixnum) in                                  
                         let tagnew =TagRef newname in
                         tagnew)
                   |TaggedSexpr(name,expr)->if(List.mem name !lstoftags)
                   then (let pre var= if(var=name) then true else false in
                   let numofTag= (List.length(List.filter pre !lstoftags)) in
                   lstoftags := name::!lstoftags;
                   let fixexpr= (insidefix expr lstoftags) in
                   let tagnew =TaggedSexpr(name^(string_of_int numofTag),fixexpr) in
                   tagnew)
                   else (let pre var= if(var=name) then true else false in
                   let numofTag= (List.length(List.filter pre !lstoftags))+1 in
                   lstoftags := name::name::!lstoftags;
                   let fixexpr= (insidefix expr lstoftags) in
                   let tagnew =TaggedSexpr(name^(string_of_int numofTag),fixexpr) in
                   tagnew)
                   
                   | Bool(b1)->Bool(b1)
                   | Nil-> Nil
                   | Number(n)->Number(n)
                   | Char(c1)->Char(c1)
                   | String(s1)->String(s1)
                   | Symbol(s1)->Symbol(s1)
                   |Pair(a ,b)->(let fixa=insidefix a lstoftags in
                               let fixb=insidefix b lstoftags in
                               let pairfix=(Pair(fixa,fixb)) in
                               pairfix)    
                  

let deal_with_tagged lst = 
  let fixlst= [] in
  let lstoftags= build_lst_names lst in
  let rec tag_numbers lst fixlst lstoftag=
     match lst with
    |[]-> fixlst
    |hd::tl-> (match hd with
                          |Nil->fixlst
                          |TagRef(name)->if(List.mem name !lstoftags)
                            then (let pre var= if(var=name) then true else false in
                                  let numofTag= (List.length(List.filter pre !lstoftags)) in
                                  let fixnum= if(numofTag==1) then 1 else (numofTag-1) in                        
                                  let newname=name^(string_of_int fixnum) in                                  
                                  let tagnew =TagRef newname in
                                  let fixlst=fixlst@[tagnew] in
                                  (tag_numbers tl fixlst lstoftag))
                                  else (let pre var= if(var=name) then true else false in
                                  let numofTag= (List.length(List.filter pre !lstoftags)) in
                                  let fixnum= if(numofTag=0) then 1 else (numofTag) in                        
                                  let newname=name^(string_of_int fixnum) in                                  
                                  let tagnew =TagRef newname in
                                  let fixlst=fixlst@[tagnew] in
                                  (tag_numbers tl fixlst lstoftag))
                          |TaggedSexpr(name,expr)-> if(List.mem name !lstoftags)
                              then (let pre var= if(var=name) then true else false in
                                    let numofTag= (List.length(List.filter pre !lstoftags)) in
                                    (*let fixexprpair=bld_pair_frm_lst fixexprlst *)
                                    (*here i need to handle with the inside of the tagged*)
                                    lstoftags := name::!lstoftags;
                                    let fixexpr= insidefix expr lstoftags in
                                    let tagnew =TaggedSexpr(name^(string_of_int numofTag),fixexpr) in
                                    let fixlst=fixlst@[tagnew] in
                                    (tag_numbers tl fixlst lstoftag))
                             else (let pre var= if(var=name) then true else false in
                             let numofTag= (List.length(List.filter pre !lstoftags))+1 in
                             (*let fixexprpair=bld_pair_frm_lst fixexprlst *)
                             (*here i need to handle with the inside of the tagged*)
                             lstoftags := name::(name::!lstoftags);
                             let fixexpr= insidefix expr lstoftags in
                             let tagnew =TaggedSexpr(name^(string_of_int numofTag),fixexpr) in
                             let fixlst=fixlst@[tagnew] in
                             (tag_numbers tl fixlst lstoftag))
                          |Pair(a,b)->let fixa=insidefix a lstoftags in
                                      let fixb= insidefix b lstoftags in
                                      let fixpair= Pair(fixa,fixb) in
                                      let fixlst=fixlst@[fixpair] in
                                      (tag_numbers tl fixlst lstoftag)
                          
                            |other-> let fixlst=fixlst@[other] in
                            (tag_numbers tl fixlst lstoftag))
      in
     tag_numbers lst fixlst lstoftags;;

(************************************fix tagged list for code-gen********************************)

let read_sexpr1 string = 
let readed_val=(not_followed_by _Sexpr_  _Sexpr_ (string_to_list string)) in 
match readed_val with
| (expr,[]) -> expr 
| (expr,rest) -> raise PC.X_no_match;;

let read_sexpr2 s=
  let sexpr_before_rename=read_sexpr1 s in
  let makelistfrmsexpr=[sexpr_before_rename] in
  let list_after_rename= deal_with_tagged makelistfrmsexpr in
  let make_sexpr_frm_lst= match list_after_rename with |[]-> Nil
                                                       |hd::tl->hd
                                                       in
                                                      
  make_sexpr_frm_lst;;

let read_sexpr s=
  let sexp=read_sexpr2 s in
  if (makeEmptyList sexp) then (read_sexpr2 s)
  else (raise X_this_should_not_happen);;

let read_sexprs1 string = 
if (String.length string)==0 then [] else
(reading_str  (string_to_list string) []);;  

let read_sexprs2 s = 
  let list_before_rename=read_sexprs1 s in
  let list_after_rename= deal_with_tagged list_before_rename in
  list_after_rename;;

let read_sexprs s=
  let listsxpr=read_sexprs2 s in
  let listbool= (List.map (makeEmptyList) listsxpr) in
  let boolforall=(List.mem false listbool) in
  if (boolforall) then (raise X_this_should_not_happen)
  else (read_sexprs2 s);;
 end;;     
 (*struct Reader *)
