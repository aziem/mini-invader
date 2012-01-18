open Global;;
open Parsetree;;
open Heapstuff;;
let print_exp exp = match exp with 
	| Var(v) -> Printf.printf "%s" v
	| VarPrime(v) -> Printf.printf "%s'" v
	| Null -> Printf.printf "NULL";;


let equiv_class_to_string eq = 
	let e = String.concat " " (List.map exp_to_string eq) in 
	"["^e^"]";;
(*
let pureheap_to_string pure = 
	match pure with 
		| Eq(e,e') -> String.concat "" [(exp_to_string e);" = ";(exp_to_string e')]
		| Topp -> "T";;
*)

let pureheap_to_string pure = 
	String.concat " " (List.map equiv_class_to_string pure);;

let spheap_to_string sp = 
	match sp with 
		| Pointsto(e,e') -> String.concat "" [(exp_to_string e); " -> ";(exp_to_string e')]
		| ListSeg(e,e') -> String.concat "" ["ls(";(exp_to_string e);",";(exp_to_string e');")"]
		| Junk -> "Junk"
		| Tops -> "T"
		| Emp -> "[]"

let symheap_print symheap = 
        let (pure,sp) = symheap in 
        let purestring = pureheap_to_string pure in 
	let spstring = List.map spheap_to_string sp in 
        let str1 = (*String.concat " & " *)purestring in 
        let str2 = String.concat " * " spstring in 
	Printf.printf "[";Printf.printf "%s" str1; Printf.printf " | "; Printf.printf "%s" str2; Printf.printf "]";
	Printf.printf "\n";;

let print_symheap_lst lst = List.map symheap_print lst;;

let print_results arr = 
	let i = ref 1 in 
	while (!i < (Array.length arr)) do 
		Printf.printf "%i.   " !i; 
	 	Printf.printf "\n";
		print_symheap_lst (arr.(!i));
		i := !i + 1;
		Printf.printf "\n";
	done;;

let print_spaces i = 
	let j = ref 1 in 
	while (!j <= i) do 
		Printf.printf "   ";
		j := !j +1;
	done;;

let rec print_inv res1 res2 stat = 
	match stat with 
		| While(_,l,s) -> Printf.printf "%i: \n" l; print_symheap_lst (res1.(l)); print_inv res1 res2 s
		| Seq(s1,s2) -> print_inv res1 res2 s1;print_inv res1 res2 s2;
		| If(_,_,s1,s2) -> print_inv res1 res2 s1;(print_inv res1 res2 s2);
		| _ -> ();;


let print_boolexp bexp = match bexp with
	| NonDet -> Printf.printf "*"
	| True -> Printf.printf "True"
	| False -> Printf.printf "False"
	| Equal(e,e') -> print_exp e; Printf.printf " = ";print_exp e'
	| NotEqual(e,e') -> print_exp e; Printf.printf " != ";print_exp e';;
	

let rec print_stat indent stat = match stat with 
	| Skip(l) -> print_spaces indent; Printf.printf "%i: Skip" l; Printf.printf "\n"
	| Goto(i,l) -> print_spaces indent; Printf.printf "%i: Goto %i\n" l i
	| Return(e,l) -> print_spaces indent; Printf.printf "%i: Return " l; print_exp e; Printf.printf ";\n"
	| Assign(e,e',l) -> print_spaces indent; Printf.printf "%i:" l;print_exp e; Printf.printf " := "; print_exp e'; Printf.printf ";"; Printf.printf "\n"
	| Lookup(e,e',l) ->  print_spaces indent; Printf.printf "%i:" l;print_exp e; Printf.printf " := "; Printf.printf "[";print_exp e';Printf.printf "]"; Printf.printf ";";Printf.printf "\n"
	| Mutate(e,e',l) -> print_spaces indent; Printf.printf "%i:" l;Printf.printf "[";print_exp e; Printf.printf "]";Printf.printf " := "; print_exp e';Printf.printf ";"; Printf.printf "\n"
	| New(e,l) -> print_spaces indent; Printf.printf "%i:" l;Printf.printf "New "; print_exp e; Printf.printf "\n"
	| Disp(e,l) -> print_spaces indent; Printf.printf "%i:" l;Printf.printf "Disp " ; print_exp e; Printf.printf "\n"
        | Seq(s1,s2) -> print_stat indent s1; print_stat indent s2;
	| If(b,l,s1,s2) -> print_spaces indent; Printf.printf "%i:" l;Printf.printf "If("; print_boolexp b; Printf.printf ") {\n";
			   print_stat (indent+1) s1; Printf.printf "} else {\n"; print_stat (indent+1) s2; Printf.printf "} \n";
	| While(b,l,s) -> print_spaces indent; Printf.printf "%i:" l;Printf.printf "While ("; print_boolexp b; Printf.printf ") { \n"; print_stat (indent+1) s; Printf.printf "} \n";
	



