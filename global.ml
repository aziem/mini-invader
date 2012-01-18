(* Global definitions *)
(* defns for the parser *)
type identifier = 
  | Vari of string
  | PrimedVar of string

type expression =  
  | Nil
  | Identifier of identifier


(* my stuff *)
type var = string;;
type label = int;;
type exp = Var of var | VarPrime of var | Null
and bexp = True | False | NonDet | Equal of exp * exp | NotEqual of exp * exp;;


let exp_to_string exp = match exp with
	| Var(v) -> v
	| VarPrime(v) -> String.concat "" [v;"'"]
	| Null -> "0";;
