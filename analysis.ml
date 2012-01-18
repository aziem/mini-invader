(* The analysis is performed here *)
open Gensym;;
open Global;;
open Parsetree;;
open Symbexec;;
open Heapstuff;;

module LabelSet = 
	Set.Make(struct 
		type t = label 
		let compare = compare
		end)



type blocks = St of stat | Bl of bexp;;
module BlockSet = 
	Set.Make(struct 
		type t = stat
		let compare = compare
		end)

type edge = label * label * bool;;

module FlowSet = 
         Set.Make(struct
                 type t = edge
                 let compare = compare
                 end)

(* modify to use lists instead of sets *)

let rec labels stat = match stat with 
	| Skip(l) -> LabelSet.add l (LabelSet.empty)
	| Goto(_,l) -> LabelSet.add l (LabelSet.empty)
	| Return(_,l) -> LabelSet.add l (LabelSet.empty)
	| Assign(_,_,l) -> LabelSet.add l (LabelSet.empty) 
       	| Lookup(_,_,l) -> LabelSet.add l (LabelSet.empty) 
	| Mutate(_,_,l) -> LabelSet.add l (LabelSet.empty) 
	| New(_,l) -> LabelSet.add l (LabelSet.empty) 
	| Disp(_,l) -> LabelSet.add l (LabelSet.empty) 
	| Seq(s1,s2) -> LabelSet.union (labels s1) (labels s2)
	| If(_,l,s1,s2) -> LabelSet.add l (LabelSet.union (labels s1) (labels s2)) 
	| While(_,l,s) -> LabelSet.add l (labels s);; 

let get_prog_stat label prog = 
	let rec _get_prog label prog = 
		match prog with 
			| Skip(l) as n -> if l = label then [n] else []
			| Goto(_,l) as n -> if l = label then [n] else []
			| Return(_,l) as n -> if l = label then [n] else []
			| Assign(_,_,l) as n-> if l = label then 
					           [n]
						else []
			| Lookup(_,_,l) as n-> if l = label then 
					           [n]
						else []
			| Mutate(_,_,l) as n-> if l = label then 
					           [n]
						else []
			| New(_,l) as n-> if l = label then 
					           [n]
						else []
			| Disp(_,l) as n-> if l = label then 
					           [n]
						else []
			| Seq(s1,s2) -> let t1 = _get_prog label s1 in 
					let t2 = _get_prog label s2 in 
					t1@t2 
                        | If(_,l,s1,s2) as n-> if label = l then [n] else 
                                           let t1 = _get_prog label s1 in 
					   let t2 = _get_prog label s2 in 
					   t1@t2 
                        | While(_,l,s2) as n -> if label = l then [n] 
                                                else 
                                                        let t2 = _get_prog label s2 in 
					                t2 
	in 
	List.hd (_get_prog label prog);;



let rec init stat = match stat with 
	| Skip(l) -> l
	| Goto(_,l) -> l
	| Return(_,l) -> l
	| Assign(_,_,l) -> l
        | Lookup(_,_,l) -> l 
	| Mutate(_,_,l) -> l 
	| New(_,l) -> l 
	| Disp(_,l) -> l 
	| Seq(s1,s2) -> (init s1) 
	| If(_,l,_,_) -> l
	| While(_,l,_) -> l;;

let final stat = 
	let rec body_has_return stat = 
		match stat with 
			| Return(_,l) -> LabelSet.add l (LabelSet.empty)
			| Seq(s1,s2) -> LabelSet.union (body_has_return s1) (body_has_return s2)
			| If(_,_,s1,s2) -> LabelSet.union (body_has_return s1) (body_has_return s2)
			| While(_,_,s) -> body_has_return s
			| _ -> LabelSet.empty 
	in
	let rec _final stat set = match stat with 
		| Skip(l) -> LabelSet.add l set
		| Goto(_,l) -> LabelSet.add l set
		| Return(_,l) -> LabelSet.add l set
		| Assign(_,_,l) -> (LabelSet.add l set)
		| Lookup(_,_,l) -> LabelSet.add l set
	        | Mutate(_,_,l) -> LabelSet.add l set
	        | New(_,l) -> LabelSet.add l set
	        | Disp(_,l) -> LabelSet.add l set
		| Seq(Return(_,l),s2) -> LabelSet.add l (_final s2 set)
                | Seq(s1,s2) -> _final s2 set 
		| If(_,_,s1,s2) -> LabelSet.union (_final s1 set) (_final s2 set) 
		| While(_,l,s) -> LabelSet.union (body_has_return s) (LabelSet.add l set)
	in 
		_final stat (LabelSet.empty);;

let blocks stat = 
	let rec _blocks stat set = match stat with
		| Skip(l) as n -> (BlockSet.add n set) 
		| Goto(_,l) as n -> (BlockSet.add n set) 
		| Return(_,l) as n -> (BlockSet.add n set) 
		| Assign(_,_,l) as n -> (BlockSet.add n set)
                | Lookup(_,_,l) as n -> (BlockSet.add n set)
                | Mutate(_,_,l) as n -> (BlockSet.add n set)
                | New(_,l) as n -> (BlockSet.add n set)
                | Disp(_,l) as n -> (BlockSet.add n set)
                | Seq(s1,s2) -> BlockSet.union (_blocks s1 set) (_blocks s2 set) 
		| If(b,_,s1,s2) as n -> BlockSet.add n (BlockSet.union (_blocks s1 set) (_blocks s2 set)) 
		| While(b,l,s) as n -> BlockSet.add n (BlockSet.add s set)
	in 
		_blocks stat (BlockSet.empty);;

let getblock l blockset = 
		let blocklist = BlockSet.elements blockset in 
		let f l1 x = match x with 
			| Skip(l2) -> l1 = l2
			| Goto(_,l2) -> l1 = l2
			| Return(_,l2) -> l1 = l2
			| Assign(_,_,l2) -> l1 = l2
                        | Lookup(_,_,l2) -> l1 = l2
			| Mutate(_,_,l2) -> l1 = l2
			| New(_,l2) -> l1 = l2
			| Disp(_,l2) -> l1 = l2
			| If(_,l2,_,_) -> l1 = l2
			| While(_,l2,_) -> l1 = l2
			| _ -> false in
		List.find (f l) blocklist;;

let rec lst2flowset lst = match lst with
		[] -> FlowSet.empty
	      | hd::tl -> FlowSet.add hd (lst2flowset tl);;


let rec flow stat = 
	let pairup label stat = let lstelmts = LabelSet.elements (final stat) in 
		 let f x y = (y,x,false) in 
		 List.map (f label) lstelmts in 
	match stat with
	| Skip(_) -> FlowSet.empty
	| Return(_,_) -> FlowSet.empty
	| Goto(i,l) -> FlowSet.add (i,l,false) (FlowSet.empty)
	| Assign(_,_,_) -> FlowSet.empty
        | Lookup(_,_,_) -> FlowSet.empty
	| Mutate(_,_,_) -> FlowSet.empty
	| New(_,_) -> FlowSet.empty
	| Disp(_,_) -> FlowSet.empty
	| Seq(Return(_,l),s2) -> let n = flow s2 in 
				 n
	| Seq(s1,s2) -> let n = (FlowSet.union (flow s1) (flow s2)) in 
		 	let s1s2edge = lst2flowset (pairup (init(s2)) s1) in 
			FlowSet.union n s1s2edge 
	| If(b,l,s1,s2) -> let n = (FlowSet.union (flow s1) (flow s2)) in
		 	   let if1edge = (l,(init s1),true) in 
			   let if2edge = (l,(init s2),false) in 
			   FlowSet.add if1edge (FlowSet.add if2edge n)	
	| While(b,l,s) -> let initflow = (l,init(s),true) in 
			  let sflow = flow s in 
			  (*let s2whileflow = lst2flowset (pairup (init(s)) s)
                           * in*) 
			  let s2whileflow = lst2flowset (pairup l s) in 
                          (*FlowSet.add initflow (FlowSet.union sflow s3whileflow);;*)	
			  FlowSet.add initflow (FlowSet.union sflow s2whileflow);;	

let reverseflow stat = let flows = flow stat in 
		       let flowelemnts = FlowSet.elements flows in 
		       let f (x,y,b) = (y,x,b) in 
		       let reverseflowelemnts = List.map f flowelemnts in 
		       lst2flowset reverseflowelemnts;;	


let flowfindpairs initvalue flowset = 
	let flowlist = FlowSet.elements flowset in
	let f l = match l with 
		(l1,l2,b) -> l1 = initvalue 
	 	| _ -> false
	in 
		List.filter f flowlist;;


(* oh no *)

(* Pure heap constructors *)
(* TODO need to write a function which takes a list of symheaps and then
   symb executes/rearranges and then abstracts *)
let analysis comm lstsymheap (ifbool:bool) = 
	let _analysis comm symheap = 
		let rearranged_symheaplst = remove_duplicates (rearrange comm symheap) in 
		let symexecuted_symheaplst = remove_duplicates (List.flatten (List.map
                (symb_execute comm ifbool) rearranged_symheaplst)) in 
		let abstracted_symheaplst = List.map (apply_abstraction) symexecuted_symheaplst in 
		remove_duplicates (abstracted_symheaplst)
	in 
	List.flatten (List.map (_analysis comm) lstsymheap);;

let pure = [Eq(Var("x"),Var("u"))];;
let sp = [Pointsto(Var("y"),VarPrime("z"));Pointsto(VarPrime("z"),Var("x"));Pointsto(Var("u"),Var("s"))];;
let comm2 = Disp(Var("x"),2);;
let comm1 = Lookup(Var("t"),Var("x"),1);;
let sp1 = [ ListSeg(Var("x"),Var("y"));Pointsto(Var("y"),Null)];;
let lst1 = ([],[ListSeg(Var("c"),Null)]);;

let my_fst triple = match triple with 
        (a,b,c) -> a;;

let my_snd triple = match triple with 
        (a,b,c) -> b;;

let my_thrd triple = match triple with 
        (a,b,c) -> c;;

let finish_analysis results prog = 
	let l = Array.length (!results) in 
	let ctr = ref 1 in
	let comm1 = ref (Skip(1)) in 
	while (not ((!ctr) = (l))) do
		comm1 := get_prog_stat !ctr (prog); 
		(!results).(!ctr) <- analysis  (!comm1) ((!results).(!ctr)) (true);
		ctr := !ctr + 1;
	done;
	results;; 

(* computes the mfp soluion for the analysis *)
let mfp_solution stat precond = 
	let init_value = precond in  
	let flowset = flow stat in 
	let flowlist = FlowSet.elements flowset in 
        let flowlist2 = ref flowlist in
        let labelset = labels stat in 
	let numlabels = List.length (LabelSet.elements labelset) + 1 in
	let blocks = blocks stat in 
	let initlabel = init stat in 
	let finallabels = final stat in 
	let worklist = ref [] in 
	let results = ref (Array.make numlabels []) in
	let results2 = ref (Array.make numlabels []) in
	let l = ref 1 in 
	let l' = ref 2 in 
        let ifbool = ref false in
	let tmp = ref [] in
	let comm1 = ref (Assign(Var("x"),Var("y"),1)) in 
	(!results).(initlabel) <- init_value; 
	worklist := flowlist;
	while (not ((List.length (!worklist)) = 0)) do 
		l := my_fst (List.hd !worklist);
		l' := my_snd (List.hd !worklist);
                ifbool := my_thrd (List.hd !worklist);
		comm1 := get_prog_stat !l (stat);
		worklist := List.tl (!worklist);
		tmp := remove_duplicates (analysis ((!comm1):stat) ((!results).(!l)) (!ifbool));
		if not (subset !tmp ((!results).(!l'))) then
			begin
				(!results).(!l') <- ((!tmp)@((!results).(!l')));
				worklist := (!worklist)@(flowfindpairs !l' flowset);
			end
	done;
	results := Array.map remove_duplicates !results;
	results2 := Array.copy !results;
	results2 := Array.map remove_duplicates !(finish_analysis results2 stat);
	(!results,!results2);;

let comm1 = Assign(Var("t"),Var("c"),2);;
let comm2 = Lookup(Var("c"),Var("c"),3);;
let comm3 = Disp(Var("t"),4);;
let prog =
        While(NotEqual(Var("c"),Null),1,Seq(comm1,Seq(comm2,comm3)));;

let prog2 = Seq(Assign(Var("p"),Null,1), While(NotEqual(Var("c"),Null),2,Seq(Lookup(Var("n"),Var("c"),3),Seq(Mutate(Var("c"),Var("p"),4),Seq(Assign(Var("p"),Var("c"),5),Assign(Var("c"),Var("n"),6))))));;

let precond2 = [([],[ListSeg(Var("c"),Null)])];;

let prog3 = Seq(Assign(Var("t"),Var("c"),1),Lookup(Var("c"),Var("c"),2));;

(*let _ = mfp_solution prog2 precond2;;*)

(*let _ = rearrange_name (get_prog_stat 3 prog2) ([Eq (Var "c", Var "n")],  [ListSeg (Var "n", Null); Pointsto (Var "p", Null)]);;*)
(*let _ = abs1 ([Eq (Var "c", Var "n")],[ListSeg (Var "p", VarPrime "x35"); Pointsto (VarPrime "x35", Null); ListSeg (Var "n", Null)]);;*)
let rec get_while_labels prog = 
	match prog with 
		| Skip(l) -> []
		| Assign(_,_,l) -> []
		| Lookup(_,_,l) -> []
	        | Mutate(_,_,l) -> []
	        | New(_,l) -> []
	        | Disp(_,l) -> []
                | Seq(s1,s2) -> (get_while_labels s1)@(get_while_labels s2) 
		| If(_,_,s1,s2) -> (get_while_labels s1)@(get_while_labels s2)
		| While(_,l,s) -> l::(get_while_labels s);;
	

let get_invariant prog res1 res2 = 
	let lbls = get_while_labels prog in 
	let rec _get_inv lbls_lst = match lbls_lst with 
		| [] -> []
		| i::tl -> let res_i = res1.(i) in 
                           (res_i)@(_get_inv tl)
	in 
	_get_inv lbls;;

let invert_bool bool = match bool with 
	| Equal(b,b') -> NotEqual(b,b') 
	| NotEqual(b,b') -> Equal(b,b') 
	| False -> True
	| True -> False;;

let get_postcondition prog res1 res2 = 
	let bool_filter bool symheap = 
		let (pure,spatial) = symheap in 
		match bool with 
			| Equal(e,e') -> var_equivelant pure e e'
			| NotEqual(e,e') -> not (var_equivelant pure e e') 
			| False -> false
			| True -> true
	in
	let _getpc prog label = 
		let comm = get_prog_stat label prog in 
		match comm with 
			| While(b,l,_) -> let inv_bool = invert_bool b in 
				  let results = res1.(l) in 
				  List.filter (bool_filter inv_bool) results 
		  	| _ -> res2.(label) 
	in
	let rec get_results final_labs = match final_labs with 
		| [] -> [] 
		| l::tl ->  (_getpc prog l)@(get_results tl) in
	let final_labs = LabelSet.elements (final prog) in
	get_results final_labs;;

