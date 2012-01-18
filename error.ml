(*****************************************************************************)
(* Exceptions                                                                *)
(*****************************************************************************)

(* Lexer *)
exception Illegal_character
exception Unterminated_comment

(* Temporary *)
exception NotImplemented

exception ErrorFound

exception Illegal_argument
exception NoUnprimedVar

exception UndefFunction of string
exception InternalError of string
exception WrongParameterNumber
exception InputError of string
