(*****************************************************************************)
(* Datatypes for parse trees and internal representations                    *)
(*****************************************************************************)

open Global

(*****************************************************************************)
(* Parse trees                                                               *)
(*****************************************************************************)

type space_pred = 
  | SpacePredEmpty
  | SpacePredPointsTo of identifier * expression
  | SpacePredListseg of expression * expression

type pure_pred = 
  | PurePredEquality of expression * expression

type assertion = 
  | Assertion of pure_pred list * space_pred list

type condition = 
  | IfEqual of expression * expression
  | IfUnequal of expression * expression
  | NondetChoice
  | STrue
  | SFalse

type statement =
  | StmtSkip
  | StmtAssign of identifier * expression
  | StmtLookup of identifier * identifier
  | StmtMemAssign of identifier * expression
  | StmtDispose of identifier
  | StmtNew of identifier
  | StmtBlock of statement list
  | StmtIf of condition * statement * statement
  | StmtWhile of condition * statement 
  | StmtGoto of int
  | StmtReturn of expression;;

type fun_decl = 
  | FunDecl of string * identifier list * statement list

type program = fun_decl list

(*****************************************************************************)
(* Internal representation of assertions                                     *)
(*****************************************************************************)
type pure_heap = Eq of exp * exp | Topp;;

type spatialheap = Pointsto of exp * exp | ListSeg of exp * exp | Junk | Emp | Tops;;

type symbheap = pure_heap list * spatialheap list;;

type stat =  
	  Assign of exp * exp * label 
        | Lookup of exp * exp * label
        | New of exp * label 
        | Disp of exp * label
        | Mutate of exp * exp * label 
	| Seq of stat * stat 
	| If of bexp * label * stat * stat 
	| While of bexp * label * stat 
	| Skip of label 
	| Return of exp * label
	| Goto of int * label;;


let primitive_command comm = 
        match comm with 
                | Assign(x,_,_) -> (false,x)
                | Lookup(_,x,_) -> (true,x)
                | Mutate(x,_,_) -> (true,x)
                | New(x,_) -> (false,x)
                | Disp(x,_) -> (true,x)
                | _ -> (false,Var("y"));;



