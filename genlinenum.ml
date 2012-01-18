
module type GENLINENUM =
sig
val reset : unit -> unit
val next : unit -> int
end ;;

module Genlinenum : GENLINENUM =
struct
let c = ref 0
let reset () = c:=0
let next () = incr c;!c
end;;
