(**
   Runs Silvia's grid_world searches.
*)

open Printf
open Scanf
open Camlish

(* Parse the command-line options. *)
let parse_params () =
  let alg_name = ref ""
  and domain_name = ref ""
  and domain_params = ref ""
  and dryrun = ref false
  and force = ref false
  and suffix = ref ".bin" in
  let parse_domain_params dp =
    let rec parse_pairs ?(accum=[]) pairs =
      match pairs with
	| [] -> accum
	| hd :: tl -> begin
	    match Str.split (Str.regexp "=") hd with
	      | a :: b :: [] -> parse_pairs ~accum:((a, b) :: accum) tl
	      | _ -> failwith (sprintf "Bad key=value pair: %s\n" hd)
	  end
    in parse_pairs (Str.split (Str.regexp ",") dp)
  in
  let usage_string =
    "Usage: run <domain> <algorithm> "
    ^ "       [-dattrs <domain parameters>]"
  in Arg.parse
       [("-dattrs",
	 Arg.Set_string domain_params,
	 "Domain specific key=value pair list (seperated by commas)");
	("-dry-run",
	 Arg.Set dryrun,
	 "Do not write any output, just run and verify the solution");
	("-force",
	 Arg.Set force,
	 "Do not skip runs for which output files already exist");
	("-suffix",
	 Arg.Set_string suffix,
	 "Domain specific key=value pair list (seperated by commas)");
       ]
       (fun p ->
	  if !domain_name = "" then domain_name := p
	  else alg_name := p)
       usage_string;
    (!alg_name, !domain_name, parse_domain_params !domain_params,
     !dryrun, !force, !suffix)


let rec exclusive_access () =
  (** Wait until we are the only user on the system. *)
  let username = Sys.getenv "USER" in
  let other_users () =
    List.fold_left
      (fun prev line -> match Str.split (Str.regexp " ") line with
	 | hd :: tl when hd <> username -> true
	 | _ -> prev)
      false
      (!! {(cmd "w -h") with pout = pout_lines})
  in if other_users () then begin
      printf "-- Sleeping while there are users logged in\n%!";
      while other_users () do
	Unix.sleep 1
      done;
      decrease_load ()
    end else ()

and decrease_load () =
  (** Wait for the load on the system to be sufficiently low. (Once it
      is low enough, we assume that no jobs are running.) *)
  let max_load = 0.05 in
  let get_load () =
    let line = !! {(cmd "w | head -n 1") with pout = pout_string} in
      match List.rev (Str.split (Str.regexp " ") line) with
	| a :: b :: c :: tl -> sscanf c "%f," (fun f -> f)
	| _ -> failwith (sprintf "Invalid output from w: [%s]" line) in
  let cur_load = get_load () in
    if cur_load > max_load then begin
      printf "-- Sleeping while the load is %f > %f\n%!" cur_load max_load;
      while (get_load ()) > max_load do
	Unix.sleep 10
      done;
      exclusive_access ()
    end else ()

let bad_lines lines =
  (** Test if there are output lines that specify this as a bad
      run.  *)
  lines = []
  || (List.exists
	(fun l ->
	   let no_sol = Str.regexp_string "No Solution" in
	     (Str.string_match no_sol l 0))
	lines)

let do_output num lines out_file out_attrs =
  (** Output the results to an RDB database. *)
  if bad_lines lines then begin
    printf " failed:\n";
    List.iter (printf "%s\n") lines
  end else begin
    let buf = Buffer.create 100
    and mach_id =
      (!! {(cmd "hostname") with pout = pout_string})
      ^ "."
      ^(!! {(cmd "domainname") with pout = pout_string})
      ^ "-"
      ^(!! {(cmd "uname -a") with pout = pout_string})
      ^ "-"
      ^(!! {(cmd "uname -s") with pout = pout_string})
      ^ "-"
      ^(!! {(cmd "uname -r") with pout = pout_string}) in
    let pair key value =
      Buffer.add_string
	buf
	(sprintf "#pair \"%s\"\t\"%s\"\n" key value)
    and col_def col_names =
      Buffer.add_string buf (sprintf "#cols ");
      List.iter
	(fun n -> Buffer.add_string buf (sprintf "%s " n))
	col_names;
      Buffer.add_string buf "\n"
    and row col_vals =
      List.iter
	(fun n -> Buffer.add_string buf (sprintf "%s\t" n))
	col_vals;
      Buffer.add_string buf "\n"
    in
    let sol_found = ref false in
      Buffer.add_string buf "#start data file format 4\n";
      pair "wall start date" (!! {(cmd "date") with pout = pout_string});
      pair "wall start time" (sprintf "%f" (Unix.gettimeofday ()));
      pair "machine id" mach_id;
      List.iter (fun (k, v) -> pair k v) out_attrs;
      pair "num" num;
      List.iter
	(fun l ->
	   match Str.split (Str.regexp " ") l with
	     | "#" :: tl -> ()	(* Note: comments must start
				   with "# " not just "#". *)
	     | "cols:" :: tl -> col_def tl (* Define column names. *)
	     | "row:" :: tl -> row tl (* Define one row. *)
	     | "expansions-per-nblock:" :: vl :: [] ->
		 pair "expansions-per-nblock" vl
	     | "cost:" :: vl :: [] ->
		 pair "final sol cost" vl;
		 if vl <> "infinity" then
		   sol_found := true
	     | "length:" :: vl :: [] ->
		 pair "final sol length" vl
	     | "wall_time:" :: vl :: [] ->
		 pair "total wall time" vl
	     | "CPU_time:" :: vl :: [] ->
		 pair "total raw cpu time" vl
	     | "generated:" :: vl :: [] ->
		 pair "total nodes generated" vl
	     | "expanded:" :: vl :: [] ->
		 pair "total nodes expanded" vl
	     | "nblock-graph-creation-time:" :: vl :: [] ->
		 pair "nblock graph creation time" vl
	     | "avg-open-list-size:" :: vl :: [] ->
		 pair "ave open list size" vl
	     | "total-nblocks:" :: vl :: [] ->
		 pair "total nblocks" vl
	     | "created-nblocks:" :: vl :: [] ->
		 pair "created nblocks" vl
	     | "failed-locks:" :: vl :: [] ->
		 pair "failed locks" vl
	     | "succeeded-locks:" :: vl :: [] ->
		 pair "succeeded locks" vl
	     | "final-sol-weight:" :: vl :: [] ->
		 pair "final solution weight" vl
	     | "time-limit:" :: vl :: [] ->
		 pair "time limit" vl
	     | _ -> failwith (sprintf "Bad output line: %s" l))
	lines;
      pair "found solution" (if !sol_found then "yes" else "no");
      pair "wall finish time" (sprintf "%f" (Unix.gettimeofday ()));
      pair "wall finish date" (!! {(cmd "date") with pout = pout_string});
      Buffer.add_string buf "#end data file format 4\n";
      let out = open_out out_file in
	Buffer.output_buffer out buf;
	close_out out;
	printf " done\n"
  end


let verify_solution droot dattrs cost bound =
  (** Verify that the given cost is within the given bound from the
      optimal cost (via A* ).
  *)
  let files =
    let astar = Rdb.matching_paths droot (("alg", "astar") :: dattrs) in
      if astar = [] then
	let idastar = Rdb.matching_paths droot (("alg", "ida_star") :: dattrs) in
	  if idastar = [] then []
	  else idastar
      else astar in

    if (files <> []) then
      try
	let df = Datafile.load (List.hd files) in
	let opt_cost = Dfutils.getfloat df "final sol cost" in
	let sol = Dfutils.getstr df "found solution" in
	  if sol = "yes" && cost <> infinity then begin

	    if cost > bound *. opt_cost then begin
	      printf "Bad solution cost: cost=%f > opt=%f * %f=%f\n"
	  	cost opt_cost bound (opt_cost *. bound);
	      false
	    end else if bound = 1.0 && cost <> opt_cost then begin
	      printf "Bad solution cost: cost=%f <> opt=%f\n" cost opt_cost;
	      false
	    end else if bound = 1.0 then begin
	      printf " ...(optimal)";
	      true
	    end else begin
	      printf " ...(bounded)";
	      true
	    end

      	  end else begin
	    if cost = infinity then printf " ...(timeout)"
	    else printf " ...(not verified [No solution])";
      	    true
      	  end

      with End_of_file -> begin
    	printf " ...(not verified [End of file])";
    	true
      end

    else begin
      printf " ...(not verified [No opt. data])";
      true
    end


let main () =
  let algorithm, domain_name, domain_params,
    dryrun, force, suffix = parse_params () in
  let domain = Domain.by_name domain_name in
  let domain_params =
    if domain_params = [] then domain.Domain.params
    else [ domain_params ] in

  let march = !! { (cmd "uname -m") with pout = pout_string } in
  let bin_path = "/home/rai/eaburns/src/cpp/silvia-code/grid-search"
  and data_root = sprintf "/home/rai/group/data/%s_instances" domain_name
  and out_root = sprintf "/home/rai/eaburns/data/%s/%s" march domain_name in

    Printf.printf "bin path: %s\n" bin_path;
    Printf.printf "bin suffix: %s\n" suffix;

    let run_files command out_attrs droot dattrs optimal in_files =
      (* Run the given command on the set of input files.

	 \param dattrs -- For finding the optimal solution cost.  *)

      let out_attrs = out_attrs @ dattrs in
	List.iter
	  (fun in_file ->
	     let num = Filename.basename in_file in
	     let out_file = Rdb.path_for out_root (out_attrs @ [("num", num)])
	     in exclusive_access ();
	       printf "File: %s %!" out_file;
	       if Sys.file_exists out_file && not force then
		 printf "...skipping\n"
	       else begin
		 let command = { command with
				   pin = pin_file in_file;
				   pout = pout_lines; } in

		 let lines = !! command in
		   assert (lines <> []);
		   let bound =
		     if not optimal then try
		       float_of_string (List.assoc "wt" out_attrs)
		     with Not_found -> 1.0
		     else 1.0 in
		   let cost =
		     try
		       let line =
			 List.find
			   (fun l ->
			      match Str.split (Str.regexp " ") l with
				| "cost:" :: _ :: [] -> true
				| _ -> false) lines
		       in match Str.split (Str.regexp " ") line with
			 | _ :: c :: [] -> float_of_string c
			 | _ -> failwith "No cost output"
		     with Not_found -> failwith "No cost output"
		   in
		     if not (verify_solution
			       out_root
			       (("num", num) :: dattrs)
			       cost
			       bound) then begin
		       List.iter (printf "%s\n") lines;
		       failwith "Bad solution cost"
		     end;
		     if not dryrun then
		       do_output num lines out_file out_attrs
		     else printf " supressed\n"
	       end)
	  in_files
    in

      List.iter
	(fun dattrs ->
	   (* For each set of domain parameters *)
	   let optimal = true in
	   let in_files = Rdb.matching_paths data_root dattrs in
	     if in_files = [] then failwith "No input files"
	     else
	       run_files
		 (cmd "%s/release-search %s" bin_path  algorithm)
		 [("type", "run"); ("alg", "richter-" ^ algorithm)]
		 data_root
		 dattrs
		 optimal
		 in_files)
	domain_params
;;

let _ = main ()

(*
  Local Variables:
  compile-command: "ocm run_silvia"
  End:
*)
