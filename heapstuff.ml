open Global;;
open Gensym;;
open Parsetree;;

type pure_heap = Eq of exp * exp | Topp;;

type spatialheap = Pointsto of exp * exp | ListSeg of exp * exp | Junk | Emp | Tops;;

type symbheap = pure_heap list * spatialheap list;;
(* put this in a utlity file?*)
let remove_duplicates lst = 
	let rec _rem_dup lst newlst = 
		match lst with 
			  [] -> [] 
		        | g::tl -> if (not (List.mem g newlst)) then 
					g::(_rem_dup tl (g::newlst))
				   else 
					_rem_dup tl (newlst)
	in
		_rem_dup lst [];;

let rec has_tops sp = match sp with 
	| [] -> ([],[])
	| Tops::tl -> ([],[Tops])
	| _::tl -> has_tops tl;;


(* Translating from the naive defn of pure heaps to the 
   equivelance class version of pure heaps *)
let rec find_directly_equiv pure_heap exp = 
        match pure_heap with
                  [] -> []
                | Eq(e,e')::tl -> if (e = exp) then e'::(find_directly_equiv tl exp)
                                  else if (e' = exp) then e::(find_directly_equiv tl exp)
                                  else find_directly_equiv tl exp;;

(* very naive way of finding the equivelance class of an expression in the pure heap *)
let rec equivelance_class exp pure_heap = 
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
        remove_duplicates (dir_eqv_lst@(f dir_eqv_lst [exp]));;

let rec is_member_pure pure var = 
	match pure with 
		| [] -> false 
		| e::tl -> if (List.mem var e) then true 
			   else is_member_pure tl var;;

(* add var2 to the equiv class of var1 *)
let rec insert_in_equiv_class (pure:Global.exp list list) var1 var2 = 
	match pure with 
		| [] -> [] 
		| e::tl -> if (List.mem var1 e) then 
				(var2::e)::tl 
			   else insert_in_equiv_class tl var1 var2;;

let pure_2_equivclass pure = 	
let rec _pure_hp_2_equivclass pure newpure = 
	match pure with 
		[] -> newpure
		| Eq(e,e')::tl -> let (b1,b2) = ((is_member_pure newpure e), (is_member_pure newpure e')) in 
				  if (not b1 && not b2) then 
					let eq = equivelance_class e pure in 
				        _pure_hp_2_equivclass tl (eq::newpure) 
				  else if (b1  && not b2) then 
					(* need to add e' to equivclass of e*)
					let newpure1 = insert_in_equiv_class newpure e e' in 
					_pure_hp_2_equivclass tl newpure1 
				  else if (b2 && not b1) then 
					(* need to add e to equivclass of e'*)
					let newpure1 = insert_in_equiv_class newpure e' e in 
					_pure_hp_2_equivclass tl newpure1 
				  else 
					(* dont need to add anything *)
					_pure_hp_2_equivclass tl newpure
		| Topp::tl ->_pure_hp_2_equivclass tl newpure
	in 
	_pure_hp_2_equivclass pure [];;

let symheap_to_internal_symheap symheap = 
	let (pure,sp) = symheap in 
	((pure_2_equivclass pure),sp);;

(* Sorting functions *)
let compare_list_size l1 l2 = 
	let l1_length = List.length l1 in 
	let l2_length = List.length l2 in 
	compare l1_length l2_length;;

let sort_equiv_class e1 = List.sort compare e1;; 

let sort_pure_heap p = 
	let p' = List.map sort_equiv_class p in 
	List.sort compare_list_size p';;

let sort_spatial_heap s = List.sort compare s;;

let tidyup_pure_heap pure = 
	let rec _rem_singleton pure = match pure with 
		| [] -> []
		| e::tl -> if ((List.length e)= 1) then _rem_singleton tl 
			   else e::(_rem_singleton tl)
	in 
	_rem_singleton (sort_pure_heap pure);;

let tidyup_symheap symheap = 
	let (pure,sp) = symheap in 
	((tidyup_pure_heap pure), sort_spatial_heap sp);;

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
	let compare_pure_elements e1 e2 = 
		match (e1,e2) with 
			| (Var(x),Var(y)) as m  -> map (fst(m)) (snd(m))
			| (VarPrime(x),VarPrime(y)) as m -> map (fst m)  (snd m)
			| (Null,Null) -> true 
			| _ -> false
	in
	let compare_equivclass eq1 eq2 = forall2 compare_pure_elements eq1 eq2 
	in
	let compare_pure p1 p2 = forall2 compare_equivclass p1 p2
	in 
	let (p1,s1) = t1 in 
	let (p2,s2) = t2 in 
	(forall2 compare_equivclass (sort_pure_heap p1) (sort_pure_heap p2)) && (forall2 compare_spatial (sort_spatial_heap s1)  (sort_spatial_heap s2));;

(* Subset test for lists of symheaps *)
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

let rec var_equivelant pure var1 var2 = 
	if (var1 = var2) then true else
	match pure with 
		| [] -> false 
		| e::tl -> if (List.mem var1 e) then 
				List.mem var2 e
			   else var_equivelant tl var1 var2;;

let rec equivclass var pure = 
	match pure with 
		| [] -> [] 
		| e::tl -> if (List.mem var e) then e 
			   else equivclass var tl;;

(* SUBSTITION FUNTIONS *)
let subst_helper oldvar newvar exp1 exp2 = 
	let a = (exp1 = oldvar) in 
	let b = (exp2 = oldvar) in 
	if (a & b) then (newvar,newvar) 
	else if a then (newvar,exp2)
	else if b then (exp1,newvar)
	else (exp1,exp2);;
 
let rec subst_spatial_heap e1 e2 spatial_heap = 
        match spatial_heap with 
                  [] -> [] 
                | Pointsto(e,e')::tl -> let (newe,newe') = subst_helper e1 e2 e e' in 
				  	(Pointsto(newe,newe'))::subst_spatial_heap e1 e2 tl
                | ListSeg(e,e')::tl -> let (newe,newe') = subst_helper e1 e2 e e' in 
				  	(ListSeg(newe,newe'))::subst_spatial_heap e1 e2 tl
                | e::tl -> e::(subst_spatial_heap e1 e2 tl);;

let rec subst_in_pure_heap pureheap exp1 exp2 = 
	let rec _sub_eq_class eq = 
		match eq with 
			| [] -> []
			| e::tl -> if e = exp1 then 
					exp2::(_sub_eq_class tl)
				 else 
					e::(_sub_eq_class tl)
	in 
	match pureheap with 
		| [] -> []
		| eq::tl -> (_sub_eq_class eq)::(subst_in_pure_heap tl exp1 exp2);;


(* ST1 and ST2 rules *)
let st1_st2 symheap = 
	let (pure,sp) = symheap in 
	let primedvar_filter v = 
		match v with 
			| VarPrime(t) -> true 
			| _ -> false 
	in 
	let othervar_filter v = 
		match v with 
			| VarPrime(t) -> false 
			| _ -> true 
	in
	let remove_var_primes eq = 
		let varprime_list = List.filter primedvar_filter eq in 
		let nonvar_prime_list = List.filter othervar_filter eq in 
		(varprime_list, nonvar_prime_list) 
	in
	let rec _st1_st2_eq_class sp varprimelst newvar = 
		match varprimelst with 
			| [] -> sp 
			| v::tl -> let sp1 = _st1_st2_eq_class sp tl newvar in 
				   subst_spatial_heap v newvar sp1
	in 
	let rec _st1_st2 pure sp newpure = 
		match pure with 
			| [] -> (newpure,sp) 
			| eq::tl -> let (novarp, varp) = remove_var_primes eq in 
				    (* should have an error if List.hd returns nothing *)
				    let newsp = _st1_st2_eq_class sp novarp (List.hd varp) in 
				    _st1_st2 tl newsp (varp::newpure)
	in 
	let (p1,s1) = _st1_st2 pure sp [] in 
	((tidyup_pure_heap p1),s1);;

let gb symheap = 
	let (pure,spatial) = symheap in 
	let filtervar_sp var spa_expr = 
		match spa_expr with 
			| Pointsto(e,e') -> (e = var) || (e' = var)
			| ListSeg(e,e') -> (e = var)  || (e' = var)
			| _ -> false
	in
	let filtervar_eq var var1 = (var = var1) in 
	let rec count_occurences_in_pure pure var = match pure with 
			| [] -> 0 
			| e::tl -> let a = List.length (List.filter (filtervar_eq var) e) in 
				   let b = count_occurences_in_pure tl var in 
				   a + b	
	in
	let is_garbage var = 
		let a = List.length (List.filter (filtervar_sp var) (spatial)) in 
		let b = (count_occurences_in_pure pure var) in
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

let abs1 symheap = 
	let (pure,spatial1) = symheap in 
	let spatial = sort_spatial_heap spatial1 in 
	let filtervar_sp var spa_expr = 
		match spa_expr with 
			| Pointsto(e,e') -> (e = var) || (e' = var)
			| ListSeg(e,e') -> (e = var)  || (e' = var)
			| _ -> false
	in
	let filtervar_eq var var1 = (var = var1) in 
	let rec count_occurences_in_pure pure var = match pure with 
			| [] -> 0 
			| e::tl -> let a = List.length (List.filter (filtervar_eq var) e) in 
				   let b = count_occurences_in_pure tl var in 
				   a + b	
	in
	let is_garbage var = 
		let a = List.length (List.filter (filtervar_sp var) (spatial)) in 
		let b = count_occurences_in_pure pure var in 
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
			| e::tl -> findalloc var tl (e::newheap)
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
	let a = (pure,(_abs1 spatial [])) in
	a;;


let abs2 symheap = 
	let (pure,spatial1) = symheap in 
	let spatial = sort_spatial_heap spatial1 in 
	let filtervar_sp var spa_expr = 
		match spa_expr with 
			| Pointsto(e,e') -> (e = var) || (e' = var)
			| ListSeg(e,e') -> (e = var)  || (e' = var)
			| _ -> false
	in
	let filtervar_eq var var1 = (var = var1) in 
	let rec count_occurences_in_pure pure var = match pure with 
			| [] -> 0 
			| e::tl -> let a = List.length (List.filter (filtervar_eq var) e) in 
				   let b = count_occurences_in_pure tl var in 
				   a + b	
	in
	let is_garbage var = 
		let a = List.length (List.filter (filtervar_sp var) (spatial)) in 
		let b = (count_occurences_in_pure pure var) in
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
			| _::tl -> check_allocated var tl
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
			| e::tl -> findalloc var tl (e::newheap)
	in 
	(* rewrite this shit! u dont need to do the checks separately!! just check findalloc on newspatial@tl shld be fine *)
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
								let (var2,b3,newlst2) = findalloc (VarPrime(v)) (newspatial@tl) [] in 
								if (b3 & b1) then 
									(*ListSeg(e,var2)::(newlst2@tl)*)
									ListSeg(e,var2)::(newlst2)
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
	let sp2 = _abs2 spatial [] in
	(pure,sp2);;

let apply_abstraction symheap = 
	let continue = ref true in 
	let syhref = ref symheap in 
	let syhrefold = ref symheap in 
	while (!continue) do 
		syhref := gb(abs2(abs1(gb (st1_st2 symheap)))); 
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





(* Testing data *)			
let pure = [[VarPrime("x"); Var("p")]]
let sp = [Pointsto(VarPrime("x"),Null)];;

let sp = [Pointsto(VarPrime("y"),Null)]



