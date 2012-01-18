(* Translates from the data structure produced by the parser into 
   my own internal data structure *)
open Global;;
open Parsetree;;
open Genlinenum;;
open Heapstuff;;

let tran_id ident = match ident with 
	| Vari(v) -> Var(v)
	| PrimedVar(v) -> VarPrime(v);;

let tran_exp expr = match expr with 
	| Nil -> Null
	| Identifier(i) -> tran_id i;;


let is_skip comm = match comm with 
	| Skip(l) -> true 
	| _ -> false;;

let tran_cond cond = match cond with 
	| IfEqual(e,f) -> Equal((tran_exp e),(tran_exp f))
	| IfUnequal(e,f) -> NotEqual((tran_exp e),(tran_exp f))
	| STrue -> True 
	| SFalse -> False
	| NondetChoice -> NonDet;;
 
let rec trans_stat_lst statlst = 
	let rec remove_last_skip stat = match stat with 
		| Seq(a,b) -> if (is_skip b) then 
				a
			    else 
				Seq(a,(remove_last_skip b)) 
		| _ as n -> n
	in 
	let f a b = let a' = trans_statement a in 
	            Seq(a',b) 
	in
(*remove_last_skip (List.fold_right f statlst (Skip(1)))*)
	let rec _trans_lst lst = match lst with 
		| [] -> Skip(100)
		| e::tl -> let e' = trans_statement e in 
			    Seq(e',(_trans_lst tl))
	in
        (* ugly hack to deal with empty if branches *)
        match statlst with 
	| [] -> let l = Genlinenum.next() in Skip(l) 
	| _ -> remove_last_skip (_trans_lst statlst)
and trans_statement stat = 
	match stat with 	
	| StmtSkip -> let ctr = Genlinenum.next() in
		      Skip(ctr)
	| StmtGoto(i) -> let ctr = Genlinenum.next() in 
			Goto(i,ctr)
	| StmtAssign(e,f) -> let ctr = Genlinenum.next() in
			     let e1 = tran_id e in 	
			     let f1 = tran_exp f in 
			     Assign(e1,f1,ctr)
	| StmtLookup(e,f) -> let ctr = Genlinenum.next() in
			     let e1 = tran_id e in 
			     let f1 = tran_id f in 
			     Lookup(e1,f1,ctr)
	| StmtMemAssign(e,f) -> let ctr = Genlinenum.next() in 
			     let e1 = tran_id e in 	
			     let f1 = tran_exp f in 
			     Mutate(e1,f1,ctr)
	| StmtDispose(e) -> let ctr = Genlinenum.next() in 
			    let e1 = tran_id e in 
			    Disp(e1,ctr)
	| StmtNew(e) -> let ctr = Genlinenum.next() in
			let e1 = tran_id e in 
			New(e1,ctr) 
	| StmtBlock(b) -> trans_stat_lst b
	| StmtIf(c,e,f) -> let ctr = Genlinenum.next() in
			   let e' = trans_statement e in
			   let f' = trans_statement f in 
			   let c' = tran_cond c in 
			   If(c',ctr,e',f')
	| StmtWhile(c,s) -> let ctr = Genlinenum.next() in
			    let s' = trans_statement s in 
			    let c' = tran_cond c in 
			    While(c',ctr,s')
	| StmtReturn(e) -> let ctr = Genlinenum.next() in 
			   let e1 = tran_exp e in 
			   Return(e1,ctr);;

let tran_fun_decl f = match f with 
	| FunDecl(s,id,s') -> trans_stat_lst s';;

(* could add more error checking here? *)
let tran_program fun_decl_list = tran_fun_decl (List.hd fun_decl_list);;

let tran_pure pure = match pure with 
	| PurePredEquality(e,e') -> Eq((tran_exp e),(tran_exp e'));;

let tran_space space = match space with 
	| SpacePredEmpty -> Emp
	| SpacePredPointsTo (id,e') -> let id' = tran_id id in
				       let e'' = tran_exp e' in 
				       Pointsto(id',e'') 
	| SpacePredListseg(e1,e2) -> let e1' = tran_exp e1 in 
				     let e2' = tran_exp e2 in 
				     ListSeg(e1',e2');;

let tran_pure_lst lst = 
	List.map tran_pure lst;;

let tran_space_lst lst = 
	List.map tran_space lst;;

let tran_pred pred = 
	match pred with 
		Assertion(pure,space) -> [((tran_pure_lst pure),(tran_space_lst space))];;
