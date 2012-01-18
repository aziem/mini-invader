(* The heap manipulation functions, plus abtraction rules and other goodies *)

open Global;;
open Gensym;;
open Parsetree;;

type pure_heap = Eq of exp * exp | Topp;;

(* the error is a really bad hack to show top *)
type spatial_heap = Pointsto of exp * exp | ListSeg of exp * exp | Junk |Emp | Tops;;

type symb_heap = pure_heap list * spatial_heap list ;;

let make_pure_heap exp1 exp2 = Eq(exp1,exp2);;

let rec has_tops sp = match sp with 
	| [] -> ([],[])
	| Tops::tl -> ([Topp],[Tops])
	| _::tl -> has_tops tl;;

let rec make_pure_heap_list = function 
        | [] -> []
        | (e1,e2)::tl -> (Eq(e1,e2))::(make_pure_heap_list tl);;

let rec make_pure_heap_list2 = function 
        | [] -> []
        | (e1,e2)::tl -> (Eq(Var(e1),Var(e2)))::(make_pure_heap_list2 tl);;


let isprimevar e = match e with 
	| VarPrime(x) -> true 
	| _ -> false;;

(*
let convert_exp (e:expl) = 
	match e with 
		Varl(v) -> Var(v);;
*)
 

(* List of primed variables in a sym heap *)
(*let rec varsprime symheap = 
	let (pure,spatial) = symheap in 
	let chooser e e' = if ((isprimevar e) & (isprimevar e')) then
				[e;e']
			   else if (isprimevar e) 
				[e] 
			   else if (isprimevar e') 
				[e']
			   else []
	in
	let rec _varsp_pure p = match p with 
		| [] -> []
		| Eq(e,e')::tl -> (chooser e e')@(_varsp_pure tl)
	in
	let rec _varsp_spatial p = match p with 
		| [] -> []
		| Pointsto(e,e')::tl -> (chooser e e')@(_varsp_spatial tl) 
		| ListSeg(e,e')::tl -> (chooser e e')@(_varsp_spatial tl)
	in
	(_varsp_pure pure )@(_varsp_spatial spatial);;
		 
*)
(* Substitution for expressions *)
let subst_exp e1 e2 exp = match exp with 
          Var(e1) -> Var(e2) 
        | VarPrime(e1) -> VarPrime(e2) 
        | Null -> Null;;
              
let subst_helper oldvar newvar exp1 exp2 = 
	let a = (exp1 = oldvar) in 
	let b = (exp2 = oldvar) in 
	if (a & b) then (newvar,newvar) 
	else if a then (newvar,exp2)
	else if b then (exp1,newvar)
	else (exp1,exp2);;
 
(* Substitution in pure heap *)
let rec subst_pure_heap e1 e2 pure_heap = 
        match pure_heap with 
                  [] -> []
                | Eq(e,e')::tl -> let (newe,newe') = subst_helper e1 e2 e e' in 
				  (Eq(newe,newe'))::subst_pure_heap e1 e2 tl;;

(* Substitution is spatial heap *)
let rec subst_spatial_heap e1 e2 spatial_heap = 
        match spatial_heap with 
                  [] -> [] 
                | Pointsto(e,e')::tl -> let (newe,newe') = subst_helper e1 e2 e e' in 
				  	(Pointsto(newe,newe'))::subst_spatial_heap e1 e2 tl
                | ListSeg(e,e')::tl -> let (newe,newe') = subst_helper e1 e2 e e' in 
				  	(ListSeg(newe,newe'))::subst_spatial_heap e1 e2 tl
                | Junk::tl -> (Junk)::(subst_spatial_heap e1 e2 tl);;

let rec find_directly_equiv pure_heap exp = 
        match pure_heap with
                  [] -> []
                | Eq(e,e')::tl -> if (e = exp) then e'::(find_directly_equiv tl exp)
                                  else if (e' = exp) then e::(find_directly_equiv tl exp)
                                  else find_directly_equiv tl exp;;

(* very naive way of finding the equivelance class of an expression in the pure heap *)
let rec equivclass exp pure_heap = 
        let dir_eqv_lst = find_directly_equiv pure_heap exp in 
        let rec f lst seen = 
                match lst with 
                         [] -> []
                       | g::tl -> if (not (List.mem g seen)) then
			          let t1 = find_directly_equiv pure_heap g in 
                                  let t3 = tl@t1 in
				  let t2 = f t3 (g::seen) in 
                                  g::(t2@t1)
				  else f tl seen
        in 
        dir_eqv_lst@(f dir_eqv_lst []);;

let var_equivelant pureheap var1 var2 = 
	if (var1 = var2) then true else 
		let var1_equivclass = equivclass var1 pureheap in 
		List.mem var2 var1_equivclass;;

(* sorts a symbolic heap, placing pointso to preds first, then lsegs then junk *)
let sortsymheap sy = 
	let (p,s) = sy in 
	let rec _sep_parts lst pts lseg junk = 
			match lst with 
				| [] -> (pts,lseg,junk)
				| Pointsto(e,e')::tl -> _sep_parts tl (Pointsto(e,e')::pts) lseg junk
				| ListSeg(e,e')::tl -> _sep_parts tl pts (ListSeg(e,e')::lseg) junk
				| Junk::tl -> _sep_parts tl pts lseg (Junk::junk)
	in
	let (s1,s2,s3) = _sep_parts s [] [] [] in
	(p,(s1@s2@s3));;	

(* alpha equivelance of two symbolic heaps *)
let alpha_eq t1 t2 = 
	let h = Hashtbl.create 100 in 
	let h' = Hashtbl.create 100 in

	let map x y = 
		let y' = try Hashtbl.find h x 
			 with Not_found -> begin Hashtbl.add h x y;y end
		in
		let x' = try Hashtbl.find h' y 
			 with Not_found -> begin Hashtbl.add h' y x;x end
		in 
		x = x' & y = y'
	in 
	let forall2 f x y = try List.for_all2 f x y 
			    with Invalid_argument _ -> false 
	in 
        let rec compare_spatial t1 t2 = 
                match (t1,t2) with
                        | (Pointsto(x,y),Pointsto(u,v)) -> (map x u) & (map y v)
                        | (ListSeg(x,y),ListSeg(u,v)) -> (map x u) & (map y v)
                        | _ -> false
        in
        let rec compare_pure t1 t2 = 
                match(t1,t2) with 
                        | (Eq(x,y),Eq(u,v)) -> (map x u) & (map y v)
                        | _ -> false
        in
        let (p1,s1) = sortsymheap t1 in 
        let (p2,s2) = sortsymheap t2 in 
        (forall2 compare_pure p1 p2) & (forall2 compare_spatial s1 s2);;

let alpha_equiv t1 t2 = 
	if (alpha_eq t1 t2) then 0 
	else 1;;

(* Set for symheaps *)
module SymheapSet = Set.Make(struct 
			     type t = symb_heap 
			     let compare = alpha_equiv
			     end);;


(* removes duplicates symheaps *)
(* this is the ugliest hack I have ever done. if u dont feel sick after understanding this, then something is wrong with u *)
let remove_duplicates lstsymheap = 
	let rec _rem lst set = match lst with 
		| [] -> set
		| e::tl -> _rem tl (SymheapSet.add e set)
	in 
	SymheapSet.elements (_rem lstsymheap SymheapSet.empty);;

(* splits a spatial heap up into three parts, pts lseg and junk *)

let split_spatial s1 = 
	let rec _split s pts lseg junk = 
	match s with 
		| [] -> (pts,lseg,junk)
		| Pointsto(e,e')::tl -> _split tl (Pointsto(e,e')::pts) lseg junk
		| ListSeg(e,e')::tl -> _split tl pts (ListSeg(e,e')::lseg) junk 
		| Junk::tl -> _split tl pts lseg (Junk::junk)
	in 
	_split s1 [] [] [];;


(* checks if sh is a member of the list using alpha_eq *)

let rec is_member sh lst = 
	match lst with 
		| [] -> false 
		| sh'::tl -> if (alpha_eq sh sh') then 
				true 
			     else 	
				is_member sh tl;;



let rec subset lst1 lst2 = 
	match lst1 with 
		| [] -> true 
		| sh::tl -> if (is_member sh lst2) then 	
				subset tl lst2 
			    else false;;

(* Abtraction rules *)

(* First some helper functions *)
let check_subst_st1 c = 
	match c with 
		| Eq(_,VarPrime(e)) -> true 
		| _ -> false;;

let check_subst_st2 c = 
	match c with 
		| Eq(VarPrime(e),_) -> true 
		| _ -> false;;

(* produce the transitive closure of the pure heap given *)

let rec transitive_close pure = 
	let rec makesymheap lst = match lst with 
		[] -> []
		| e :: tl -> ([e],[Junk])::(makesymheap tl) 
	in
	let pairup e e' = Eq(e',e) in 
	let _tran lst = match lst with 
		| [] -> []
		| Eq(e,e')::tl  -> let e_equiv_class = equivclass e pure in 
			           let e'_equiv_class = equivclass e' pure in 
				   [Eq(e,e')]@(List.map (pairup e') e_equiv_class)@(List.map (pairup e) e'_equiv_class)@(transitive_close tl) 
		| Topp::tl -> [Topp]@(transitive_close tl)
	in
	List.flatten (List.map fst (remove_duplicates (makesymheap (_tran pure))));;


(* TODO *)

(* ST1 and ST2 rules *)
let st1_st2 symheap = 
	let perform_subst eqexpr spheap = 
		match eqexpr with 
			(* maybe i should make sure e' is not a primed var?*)
			| Eq(VarPrime(e),e') -> subst_spatial_heap (VarPrime(e)) e' spheap 
			| Eq(e',VarPrime(e)) -> subst_spatial_heap (VarPrime(e)) e' spheap 
			| _ -> spheap (* shouldnt happen! *)
	in
	let (pure,spatial) = symheap in 
	let spref = ref spatial in 
	let newpref = ref [] in 
	let loop_ptr = ref pure in
	let c = ref (Eq(Var("x"),Var("y"))) in
	while (not ((List.length !loop_ptr) = 0)) do 
		begin 
		c := List.hd !loop_ptr; 
		if (check_subst_st1 !c) then 
			begin
				spref := (perform_subst !c !spref);
	 		end
		else if (check_subst_st2 !c) then 
			begin	
				spref := (perform_subst !c !spref);
			end
		else 
			begin 
				(* if no sub is to be made, add to new pure heap *)
				newpref := (!c::(!newpref))
			end;
		loop_ptr := (List.tl !loop_ptr)
		end
	done;
	(!newpref,!spref)

(* GB1 rule *)
(* we can exploit the fact that for this rule to work, the primed 
variable needs to occur at least twice for it not to be junk. *)
let gb1 symheap = 
	let (pure,spatial) = symheap in 
	let filtervar_sp var spa_expr = 
		match spa_expr with 
			| Pointsto(e,e') -> (e = var) || (e' = var)
			| ListSeg(e,e') -> (e = var)  || (e' = var)
			| Junk -> false
	in
	let filtervar_pure var pure_exp = 
		match pure_exp with 
			| Eq(e,e') -> (e = var) || (e' = var)
	in
	let is_garbage var = 
		let a = List.length (List.filter (filtervar_sp var) (spatial)) in 
		let b = List.length (List.filter (filtervar_pure var) (pure)) in 
		not ((a+b)>= 2)
	in
	let rec _gb1 spatial = 
		match spatial with 
			| [] -> []
			| ListSeg(VarPrime(v),e)::tl -> if (is_garbage (VarPrime(v))) then 
								_gb1 tl 
							else 
								(ListSeg(VarPrime(v),e))::(_gb1 tl)
			| Pointsto(VarPrime(v),e)::tl -> if (is_garbage (VarPrime(v))) then 
								_gb1 tl 
							else 
								(Pointsto(VarPrime(v),e))::(_gb1 tl)
			| hd::tl -> hd::(_gb1 tl)
	in
	(pure,(_gb1 spatial));;	


(* GB2 rule *)

let gb2 symheap = 
	let (pure,spatial) = symheap in 
	let filtervar_sp var spa_expr = 
		match spa_expr with 
			| Pointsto(e,e') -> (e = var) || (e' = var)
			| ListSeg(e,e') -> (e = var)  || (e' = var)
			| Junk -> false
	in
	let filtervar_pure var pure_exp = 
		match pure_exp with 
			| Eq(e,e') -> (e = var) || (e' = var)
	in
	let is_garbage var = 
		let a = List.length (List.filter (filtervar_sp var) (spatial)) in 
		let b = List.length (List.filter (filtervar_pure var) (pure)) in 
		not ((a+b)> 2)
	in
	(* Takes an expression, and checks if the spatial list has the given expression.
	   If it does then it removes the given expression and returns the rest of the list 
	*)
	let rec has_opposite e spatiallist = 
		match spatiallist with 
			| [] -> (false,[]) 
			| e'::tl -> if (e = e') then 
					let (b,r) = has_opposite e tl in 
					(true,r) 
				    else 
					let (b,r) = has_opposite e tl in 
					(b,(e'::r)) 
	in 
	let rec _gb2 sp = 
		match sp with 
			| [] -> [] 
			| Pointsto(VarPrime(v),VarPrime(v'))::tl -> 
					(* Makes the opposite spatial exp and removes it from the rest of the list *)
					let opposite = (Pointsto(VarPrime(v'), VarPrime(v))) in 
					let (hasopposite,result) = has_opposite opposite tl in 
					(* This now checks if the current spatial expression is garbage *)
					let isjunk1 = is_garbage (VarPrime(v)) in 
					let isjunk2 = is_garbage (VarPrime(v')) in 
					(* if the opposite expr was in the list it removes it *)
					if (hasopposite & isjunk1 & isjunk2) then _gb2 result
					else (Pointsto(VarPrime(v),VarPrime(v')))::(_gb2 result) 
			| ListSeg(VarPrime(v),VarPrime(v'))::tl -> 
					let opposite = (ListSeg(VarPrime(v'), VarPrime(v))) in 
					let (hasopposite,result) = has_opposite opposite tl in 
					let isjunk1 = is_garbage (VarPrime(v)) in 
					let isjunk2 = is_garbage (VarPrime(v')) in 
					if (hasopposite & isjunk1 & isjunk2) then _gb2 tl 
					else (Pointsto(VarPrime(v),VarPrime(v')))::(_gb2 tl) 
			| e::tl -> e::(_gb2 tl)
	in
	(pure,_gb2 spatial);;

let abs1 symheap = 
	let (pure,spatial) = symheap in 
	let filtervar_sp var spa_expr = 
		match spa_expr with 
			| Pointsto(e,e') -> (e = var) || (e' = var)
			| ListSeg(e,e') -> (e = var)  || (e' = var)
			| Junk -> false
	in
	let filtervar_pure var pure_exp = 
		match pure_exp with 
			| Eq(e,e') -> (e = var) || (e' = var)
	in
	let is_garbage var = 
		let a = List.length (List.filter (filtervar_sp var) (spatial)) in 
		let b = List.length (List.filter (filtervar_pure var) (pure)) in 
		not ((a+b)> 2)
	in
	let rec findalloc var oldheap newheap =  
		match oldheap with 
			| [] -> (var,false,[]) 
			| Pointsto(e,e')::tl -> let b1 = (e = var) in 
						let b3 = not (e' = var) in 
						let b2 = var_equivelant pure e' Null in 
						if (b1 & b2 & b3 & (is_garbage var)) then 
							(Null,true,newheap@tl)
						else 
							findalloc var tl (Pointsto(e,e')::newheap)
			| ListSeg(e,e')::tl -> let b1 = (e = var) in 
						let b3 = not (e' = var) in 
						let b2 = var_equivelant pure e' Null in 
						if (b1 & b2 & b3 & (is_garbage var)) then 
							(Null,true,newheap@tl)
						else 
							findalloc var tl (ListSeg(e,e')::newheap)
			| Junk::tl -> findalloc var tl (Junk::newheap)
	in 
	let rec _abs1 oldspatial newspatial= 
		match oldspatial with 
			| [] -> newspatial
			| ListSeg(e,VarPrime(v))::tl -> let b1 = not (e = VarPrime(v)) in 
							let (var,b2,newlst) = findalloc (VarPrime(v)) tl [] in
							if (b2 & b1) then 
								ListSeg(e,var)::(newlst@newspatial)
							else 
								let (var2,b3,newlst2) = findalloc (VarPrime(v)) newspatial [] in 
								if (b3 & b1) then 
									ListSeg(e,var2)::(newlst2@tl)
								else
									_abs1 tl ((ListSeg(e,VarPrime(v)))::newspatial)
			| Pointsto(e,VarPrime(v))::tl -> let b1 = not (e = VarPrime(v)) in 
							let (var,b2,newlst) = findalloc (VarPrime(v)) tl [] in
							if (b2 & b1) then 
								ListSeg(e,var)::(newlst@newspatial)
							else 
								let (var2,b3,newlst2) = findalloc (VarPrime(v)) newspatial [] in 
								if (b3 & b1) then 
									ListSeg(e,var2)::(newlst2@tl)
								else
									(_abs1 tl ((Pointsto(e,VarPrime(v)))::newspatial))
			| e::tl -> (_abs1 tl (e::newspatial))
	in 
	(pure,(_abs1 spatial []));;


let abs2 symheap = 
	let (pure,spatial) = symheap in 
	let filtervar_sp var spa_expr = 
		match spa_expr with 
			| Pointsto(e,e') -> (e = var) || (e' = var)
			| ListSeg(e,e') -> (e = var)  || (e' = var)
			| Junk -> false
	in
	let filtervar_pure var pure_exp = 
		match pure_exp with 
			| Eq(e,e') -> (e = var) || (e' = var)
	in
	let is_garbage var = 
		let a = List.length (List.filter (filtervar_sp var) (spatial)) in 
		let b = List.length (List.filter (filtervar_pure var) (pure)) in 
		not ((a+b)> 2)
	in
	let rec check_allocated var spheap = 
		let varequivclass = equivclass var pure in 
		match spheap with 
			| [] -> false
			| Pointsto(e,e')::tl -> if ((e = var) || (List.mem e varequivclass)) then 
							true
						else 
							check_allocated var tl 
			| ListSeg(e,e')::tl -> if ((e = var) ||( List.mem e varequivclass)) then 
							true
						else 
							check_allocated var tl
			| Junk::tl -> check_allocated var tl
			in
	let rec findalloc var oldheap newheap =  
		match oldheap with 
			| [] -> (var,false,[]) 
			| Pointsto(e,e')::tl -> let b1 = (e = var) in 
						let b3 = not (e' = var) in 
						let b2 = check_allocated e' (newheap@tl)  in 
						if (b1 & b2 & b3 & (is_garbage var)) then 
							(e',true,newheap@tl)
						else 
							findalloc var tl (Pointsto(e,e')::newheap)
			| ListSeg(e,e')::tl -> let b1 = (e = var) in 
						let b3 = not (e' = var) in 
						let b2 = check_allocated e' (newheap@tl) in 
						if (b1 & b2 & b3 & (is_garbage var)) then 
							(e',true,newheap@tl)
						else 
							findalloc var tl (ListSeg(e,e')::newheap)
			| Junk::tl -> findalloc var tl (Junk::newheap)
	in 
	let rec _abs2 oldspatial newspatial= 
		match oldspatial with 
			| [] -> newspatial
			| ListSeg(e,VarPrime(v))::tl -> let b1 = not (e = VarPrime(v)) in 
							let (var,b2,newlst) = findalloc (VarPrime(v)) tl [] in
							(* check if v' is in the tl and we can remove it*)
							if (b2 & b1) then 
								ListSeg(e,var)::(newlst@newspatial)
							else 
								(* otherwise check the 'seen' elements of the heap *)
								let (var2,b3,newlst2) = findalloc (VarPrime(v)) newspatial [] in 
								if (b3 & b1) then 
									ListSeg(e,var2)::(newlst2@tl)
								else
								(* otherwise we cant apply the rule *)
									(_abs2 tl ((ListSeg(e,VarPrime(v)))::newspatial))
			| Pointsto(e,VarPrime(v))::tl -> let b1 = not (e = VarPrime(v)) in 
							(* check if v' is in the tl and we can remove it*)
							let (var,b2,newlst) = findalloc (VarPrime(v)) tl [] in
							if (b2 & b1) then 
								ListSeg(e,var)::(newlst@newspatial)
							else 
								(* otherwise check the 'seen' elements of the heap *)
								let (var2,b3,newlst2) = findalloc (VarPrime(v)) newspatial [] in 
								if (b3 & b1) then 
									ListSeg(e,var2)::(newlst2@tl)
								else
									(* otherwise we cant apply the rule *)
									(_abs2 tl ((Pointsto(e,VarPrime(v)))::newspatial))
			| e::tl -> _abs2 tl (e::newspatial)
	in 
	(pure,(_abs2 spatial []));;


let apply_abstraction symheap = 
	let continue = ref true in 
	let syhref = ref symheap in 
	let syhrefold = ref symheap in 
	while (!continue) do 
		syhref := gb2(abs2(abs1(gb1 (st1_st2 symheap)))); 
		if (!syhref = !syhrefold) then 
			continue := false
		else 
			syhrefold := !syhref
 	done;
	!syhref;;



(* Querying Rules *)

let symheap_allocated var symheap = 
	let (pure,spatial) = symheap in 
	let rec _alloc var spatial = 
		match spatial with 
			| [] -> false 
			| ListSeg(var,_)::tl -> true 
			| Pointsto(var,_)::tl -> true 
			| _::tl -> _alloc var tl 
	in 
	_alloc var spatial;;


let symheap_circ_lseg symheap = 
	let (pure,spatial) = symheap in 
	let rec _chk_circ sp = match sp with 
		| [] -> false
		| ListSeg(e,f)::tl -> if (var_equivelant pure e f) then 
					true 
				  else 
					_chk_circ tl
		| _::tl -> _chk_circ tl
	in 
	_chk_circ spatial;;


(* move this function to misc or somwhere *)

let list_remove lst elem = 
	let f e = not (elem = e) in 
	List.filter f lst;;


let symheap_alloc_twice symheap = 
	let (pure,spatial) = symheap in 
	let rec _chk_alloc varlist sp = 
		match sp with 
			| [] -> false 
			| ListSeg(e,_)::tl -> if (List.mem e varlist) then true 
					      else _chk_alloc varlist tl
			| Pointsto(e,_)::tl -> if (List.mem e varlist) then true 
					       else _chk_alloc varlist tl 
			| Junk::tl -> _chk_alloc varlist tl 
	in 
	let rec _chk_alloc_twice sp vars_seen = 
		match sp with 
			| [] -> false
			| ListSeg(e,_)::tl -> if (not (List.mem e vars_seen)) then
					      	let equiv_class = list_remove (equivclass e pure) e in 
						if (_chk_alloc equiv_class spatial) then 
							true 
				                else 
							_chk_alloc_twice tl (e::vars_seen)
					      else _chk_alloc_twice tl vars_seen
			| Pointsto(e,_)::tl -> if (not (List.mem e vars_seen)) then
					      	let equiv_class = list_remove (equivclass e pure) e in 
						if (_chk_alloc equiv_class spatial) then 
							true 
				                else 
							_chk_alloc_twice tl (e::vars_seen)
					      else _chk_alloc_twice tl vars_seen
			| Junk::tl -> _chk_alloc_twice tl vars_seen
	in 
	_chk_alloc_twice spatial [];;

let rec remove_empty_symheaps lstsymheap = 
        match lstsymheap with 
                | [] -> [] 
                | ([],[])::tl -> remove_empty_symheaps tl 
                | s::tl -> s::(remove_empty_symheaps tl);;

let symheap_asserts_false symheap = 
	let (pure,spatial) = symheap in 
	let nil_eq_class = equivclass Null pure in 
	let rec _chk_nil_alloc sp = match sp with 
		| [] -> false 
		| ListSeg(e,_)::tl -> if (List.mem e nil_eq_class) then 
			   	if (symheap_allocated e symheap) then 
					true 
			        else _chk_nil_alloc tl 
			   else 
				_chk_nil_alloc tl
		| Pointsto(e,_)::tl -> if (List.mem e nil_eq_class) then
			   	if (symheap_allocated e symheap) then 
					true 
			        else _chk_nil_alloc tl 
			   else 
				_chk_nil_alloc tl
		| Junk::tl -> _chk_nil_alloc tl
	in
	(_chk_nil_alloc spatial) || (symheap_alloc_twice symheap) || (symheap_circ_lseg symheap);;
	


(* Rearrangement Rules *)
let create_freshvar () = 
	let varstring = Gensym.next "x" in 
	VarPrime(varstring);;

let rec find_allocated var symheap = 
	match symheap with 
	| [] -> (false, Null)
	| Pointsto(e,e')::tl -> if (e = var) then 
					(true,e')
				     else
					find_allocated var tl 
	| ListSeg(e,e')::tl -> if (e = var) then 
					(true,e')
				     else
					find_allocated var tl 
	| Junk::tl -> find_allocated var tl;;

let rec dispose var oldspatial newspatial =
	match oldspatial with 
		| [] -> [Tops]
		| Pointsto(e,e')::tl -> if (e = var) then 
						newspatial@tl 
				    	else 
						dispose var tl (Pointsto(e,e')::newspatial)
		| ListSeg(e,e')::tl ->  if (e = var) then 
						newspatial@tl
				    	else 
						dispose var tl (ListSeg(e,e')::newspatial)
		| Junk::tl -> dispose var tl (Junk::newspatial);;

let rec mutate var mutatedvar oldspatial newspatial = 
	match oldspatial with 
		| [] -> [Tops]
		| Pointsto(e,e')::tl -> if (e = var) then 
						newspatial@(Pointsto(e,mutatedvar)::tl)
					else 		
						mutate var mutatedvar tl (Pointsto(e,e')::newspatial)
		| ListSeg(e,e')::tl -> if (e = var) then 
						newspatial@(ListSeg(e,mutatedvar)::tl)
					else 		
						mutate var mutatedvar tl (ListSeg(e,e')::newspatial)
		| Junk::tl -> mutate var mutatedvar tl (Junk::newspatial);;

let rearrange_name comm symheap = 
	let (pure,spatial) = symheap in
	let rec _rearrange oldvar newvar oldspatial newspatial = 
		match oldspatial with 
			| [] -> (false,newspatial)
			| Pointsto(e,e')::tl -> if e = oldvar then 
							(true,(newspatial@(Pointsto(newvar,e')::tl)))
						else 
							_rearrange oldvar newvar tl (Pointsto(e,e')::newspatial)
			| ListSeg(e,e')::tl -> if e = oldvar then 
							(true,(newspatial@(ListSeg(newvar,e')::tl)))
						else 
							_rearrange oldvar newvar tl (ListSeg(e,e')::newspatial)
			| Junk::tl -> _rearrange oldvar newvar tl (Junk::newspatial)
	in	
	let rec _perform_subst var var_equiv = 
		match var_equiv with 
			| [] -> [] 
			| v::tl -> let (stopb,newsp) = _rearrange v var spatial [] in 
				   if stopb then 
					newsp 
				   else 
					_perform_subst var tl
	in 
	let (continue,var) = primitive_command comm in 
	if (not continue) then 
		[symheap] (* no need to rearrange *)
	else 
		let (allocated,_) = find_allocated var spatial in 			
		if allocated then [symheap] 
		else 	let var_equiv_class = equivclass var pure in 
			[(pure,(_perform_subst var var_equiv_class))];;
	


let rearrange_lseg comm symheap = 
	let rec _split_list_size2 var oldsymheap newsymheap =
		match oldsymheap with 
			| [] -> newsymheap
			| ListSeg(e,e')::tl -> if (e = var) then
							let freshvar = create_freshvar() in
							let sp1 = Pointsto(e,freshvar) in 
							let sp2 = ListSeg(freshvar,e') in 
							(newsymheap)@[sp1;sp2]@tl
						else 
							_split_list_size2 var tl (ListSeg(e,e')::newsymheap)  
			| e::tl -> _split_list_size2 var tl (e::newsymheap)
	in
	let rec _split_list_size1 var oldsymheap newsymheap = 
		match oldsymheap with 
			| [] -> newsymheap 
			| ListSeg(e,e')::tl -> if (e = var) then 
					       		newsymheap@((Pointsto(e,e'))::tl)
					       else 
							_split_list_size1 var tl (ListSeg(e,e')::newsymheap)  
			| e::tl -> _split_list_size1 var tl (e::newsymheap)
	in
	let (pure,spatial) = symheap in 
	let (continue,var) = primitive_command comm in
	if (continue) then 
		let (allocated,var1) = find_allocated var spatial in 
		if (allocated) then
			(* dont need to rearrange *)
			let symheap1 = _split_list_size1 var spatial [] in 
			let symheap2 = _split_list_size2 var spatial [] in 
			(*if (symheap2 = symheap1) then 
				[(pure,symheap1)]
			else*)
				[(pure,symheap1);(pure,symheap2)]
		else 
			(* need to rename some variable using the equality from the pure part *)
			(* shouldnt really need to go here? *)
			[]
	else 
		[symheap] (* Should really raise an exception, cos somthing must have gone really wrong *);;


let rearrange comm symheap = 
	(*let t3 = Printf.printf "BEFORE \n" in 
	let t = symheap_print symheap in 
*)	let r1 = rearrange_name comm symheap in 
	let r2 = rearrange_lseg comm (List.hd (r1)) in
(*	let t4 = Printf.printf "After \n" in  
	let t2 = List.map symheap_print r2 in 
*)	r2;;


