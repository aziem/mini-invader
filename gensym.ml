(* New variable generator *)

module type GENSYM =
sig
val reset : unit -> unit
val next : string -> string
end ;;

module Gensym : GENSYM =
struct
let c = ref 0
let reset () = c:=0
let next s = incr c ; s ^ (string_of_int !c)
end;;
