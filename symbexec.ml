open Global;;
open Parsetree;;
open Heapstuff;;

 (* let boolfilter bool symheap = 
	let (pure,spatial) = symheap in 
	match bool with 
		| Equal(e,e') -> let newpure = Eq(e,e')::pure in 
			 	 let (p1,s1) = has_tops spatial in 
				 if (not (symheap_asserts_false (newpure,spatial))) then
                                         [(p1,s1);(newpure,spatial)]
                                 else
                                         [(p1,s1)]
                | NotEqual(e,e') -> let (p1,s1) = has_tops spatial in 
                                    let neq = not (var_equivelant pure e e') in 
                                    let consistent = not (symheap_asserts_false symheap) in 
                                    if (neq & consistent) then 
                                            [(p1,s1);symheap]
                                    else 
                                            [(p1,s1)]
                | True -> [symheap]
                | False -> [];;
*) 

let add_equality (pure:Global.exp list list) var1 var2 = 
	let b1 = is_member_pure pure var1 in 
	if b1 then 
		insert_in_equiv_class pure var1 var2
	else 
		let b2 = is_member_pure pure var2 in 
		if b2 then 
			insert_in_equiv_class pure var2 var1 
		else 
			[var1;var2]::pure;;


let boolfilter bool symheap = 
	let (pure,spatial) = symheap in 
	match bool with 
		| Equal(e,e') -> let newpure = add_equality pure e e' in 
			 	 let (p1,s1) = has_tops spatial in 
				 if (not (symheap_asserts_false (newpure,spatial))) then
                                         [(p1,s1);(newpure,spatial)]
                                 else
                                         [(p1,s1)]
                | NotEqual(e,e') -> let (p1,s1) = has_tops spatial in 
                                    let neq = not (var_equivelant pure e e') in 
                                    let consistent = not (symheap_asserts_false symheap) in 
                                    if (neq & consistent) then 
                                            [(p1,s1);symheap]
                                    else 
                                            [(p1,s1)]
                | True -> [symheap]
                | False -> []
		| NonDet -> [symheap];;
				
(* Symbolic Execution Rules *)
let symb_execute comm ifbool symheap = 
	let (pure,spatial) = symheap in 
	match comm with 
		| Skip(l) -> [symheap]
		| Assign(e,e',_) -> let var1 = e in 
				    let var2 = e' in 
				    let freshvar = create_freshvar () in 
				    let pure1 = pure in 
				    let newpure = subst_in_pure_heap pure1 var1 freshvar in 
				    let newspatial = subst_spatial_heap var1 freshvar spatial in 
				    let newpure1 = if (var1 = var2) then 
							add_equality newpure var1 freshvar 
						   else 
							add_equality newpure var1 var2
				    in [(newpure1,newspatial)]
				   (*  let additional_eq = if (var1 = var2) then 
								Eq(var1,freshvarek  
						        else 
								Eq(var1,var2) in
                                    [((additional_eq::newpure),newspatial)] *)
	        | Lookup(e,e',_) -> let var1 = e in 
				    let var2 = e' in 
				    let freshvar = create_freshvar () in 
				    (* check e' is allocated and get the var it is allocated to *)
				    let (alloc,f) = find_allocated var2 spatial in 
				    if (alloc) then 
				    	let pure1 = pure in 
					let newpure = subst_in_pure_heap pure1 var1 freshvar in 
					let newspatial = subst_spatial_heap var1 freshvar spatial in 
					 let newpure1 = if (var1 = f) then 
							add_equality newpure var1 freshvar 
						   else 
							add_equality newpure var1 f
				    in [(newpure1,newspatial)]
					(* 				    let add_eq = if (var1 = f) then 
							Eq(var1,freshvar) 
						     else 
							Eq(var1,f) in
                                        [((add_eq::newpure),newspatial)]
*)
				    (* write the else branch *)
                                    else [([],[Tops])]
		| New(e,_) -> let var = e in 
			      let freshvar = create_freshvar () in
			      let freshvar2 = create_freshvar () in  
			      let newpure = subst_in_pure_heap pure var freshvar in 
			      let newspatial = subst_spatial_heap var freshvar spatial in 
			      let newpts = Pointsto(var,freshvar2) in 
                              [(newpure,(newpts::newspatial))]
		| Disp(e,_) -> let var = e in 
				  let newspatial = dispose var spatial [] in 
				  if (newspatial = [Tops]) then
                                          [([],[Tops])]
				  else  
                                          [(pure,newspatial)]
		| Mutate(e,e',_) -> let var = e in
				    let var2 =e' in
				    let newspatial = mutate var var2 spatial [] in 
				    if (newspatial = [Tops]) then 
                                            [([],[Tops])] 
				    else 
                                            [(pure,newspatial)]
		| While(b,e,l) -> if (ifbool) then 
				  	remove_empty_symheaps (boolfilter b symheap)
				   else (* filter on not b *)
                                        begin
                                        match b with 
                                                | Equal(e,e') ->
                                                                (remove_empty_symheaps
                                                                (boolfilter
                                                                (NotEqual(e,e'))
                                                                symheap))
                                                | NotEqual(e,e') ->
                                                                (remove_empty_symheaps
                                                                (boolfilter
                                                                (Equal(e,e'))
                                                                symheap))
                                                | False -> 
                                                                (remove_empty_symheaps
                                                                (boolfilter
                                                                True
                                                                symheap))
                                                | True -> 
                                                                (remove_empty_symheaps
                                                                (boolfilter
                                                                False
                                                                symheap))
						| NonDet -> [symheap]
                                        end
                | If(b,e,e',l) -> if (ifbool) then (* filter on b *) 
                                        remove_empty_symheaps (boolfilter b symheap)
                                  else (* filter on not b *)
                                        begin
                                        match b with 
                                                | Equal(e,e') ->
                                                                (remove_empty_symheaps
                                                                (boolfilter
                                                                (NotEqual(e,e'))
                                                                symheap))
                                                | NotEqual(e,e') ->
                                                                (remove_empty_symheaps
                                                                (boolfilter
                                                                (Equal(e,e'))
                                                                symheap))
                                                | False -> 
                                                                (remove_empty_symheaps
                                                                (boolfilter
                                                                True
                                                                symheap))
                                                | True -> 
                                                                (remove_empty_symheaps
                                                                (boolfilter
                                                                False
                                                                symheap))
						| NonDet -> [symheap]
                                        end
					(*[symheap]*)
		| Goto(i,l) -> [symheap]
		| Return(e,l) -> [symheap]
                | _ -> [([],[])] (* should raise an exception *);;
				    


