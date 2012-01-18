(* Main file: calls all the stuff *)
open Trans;;
open Global;;
open Utils;;
open Parsetree;;
open Heapstuff;; 
open Analysis;;

let program_file_name = ref "";;
let precondition_file_name = ref "";;

let set_file_name n = program_file_name := n ;;
let set_pre_name pn = precondition_file_name := pn;;


let arg_list = [("-f", Arg.String(set_file_name), "program file name");
		("-p", Arg.String(set_pre_name), "precondition file name");]


let _ = 
  let usage_msg = "Usage: -f <file_name> -p <precondition_name>" in 
  let _ = Arg.parse arg_list (fun s -> ()) usage_msg in 
   if ((!program_file_name="") || (!precondition_file_name = "")) then
	Printf.printf "\n Program or Precondition file name not given...\n %s \n" usage_msg 
  else
(*  let anon_arg_func fname = Config.input_fname := fname in
  Arg.parse Config.speclist anon_arg_func Config.usage_msg; *)
  let ic_prog = open_in !program_file_name in
  let ic_ass = open_in !precondition_file_name in
  let lex_prog = Lexing.from_channel ic_prog in
  let lex_ass = Lexing.from_channel ic_ass in 
  let prog = Parser.program Lexer.token lex_prog in
  let _ = Printf.printf "Program parsed successfully\n" in
  let myprog = Trans.tran_program prog in 
  let ass = Parser.assertion Lexer.token lex_ass in 
  let _ = Printf.printf "Assertion parsed successfully\n" in
  let init_time = ref 0.0 in 
  let final_time = ref 0.0 in 
  let heap = List.map symheap_to_internal_symheap (tran_pred ass) in 
  close_in ic_prog;
  close_in ic_ass; 
  Printf.printf "**********************\n";
  Printf.printf "Program\n";
  Printf.printf "**********************\n";
  Printf.printf "\n";
  print_stat 0 myprog;
  Printf.printf "\n";
  Printf.printf "**********************\n";
  Printf.printf "Initial heap\n";
  Printf.printf "**********************\n";
  Printf.printf "\n";
  print_symheap_lst heap;
  Printf.printf "\n";
  init_time := Sys.time ();
  let (r1,r2) = mfp_solution myprog heap in
  final_time := Sys.time ();
  Printf.printf "**********************\n";
  Printf.printf "Results at entry points\n";
  Printf.printf "**********************\n";
  Utils.print_results r1;
  Printf.printf "\n";
  Printf.printf "**********************\n";
  Printf.printf "Results at exit points\n";
  Printf.printf "**********************\n";
  Utils.print_results r2;
  Printf.printf "\n";
  Printf.printf "\n";
  Printf.printf "**********************\n";
  Printf.printf "Invariants \n";
  Printf.printf "**********************\n";
  Utils.print_inv r1 r2 myprog;
  Printf.printf "**********************\n";
  Printf.printf "Postcondition\n";
  Printf.printf "**********************\n";
  let pc = get_postcondition myprog r1 r2 in 
  Utils.print_symheap_lst pc;
  Format.printf "Max size of major heap: %dK\n" 
  (((Gc.stat ()).Gc.top_heap_words)/256);
  Format.printf "Final minor heap size:  %dK\n" 
  (((Gc.get()).Gc.minor_heap_size)/256);
  Printf.printf "Time taken : %f \n" (!final_time -. !init_time);;


