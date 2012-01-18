
let input_fname = ref ""

let verbose = ref false

let print_context = ref false

let max_cutpoints = ref 10

let speclist = [
  ("-cutpoints", Arg.Int (fun n -> max_cutpoints := n), 
   "Maximum number of cutpoints in a symbolic heap");
  ("-v", Arg.Unit (fun () -> verbose := true), 
   "Display additional internal information");
  ("-contexts", Arg.Unit (fun () -> print_context := true), 
   "Print contexts of calls")
]

let usage_msg = "Usage: interproc [-v] [-cutpoints n] [-contexts] <file>"
