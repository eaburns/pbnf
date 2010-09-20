(**
   Algorithm specific code.
*)

open Printf
open Scripts_domain
open Camlish

(* Build a function that gets an algorithm and its info given the
   domain. *)
let march = !! {(cmd "uname -m") with pout = pout_string}

let by_name domain =
  let threads =
(*
    if march = "sun4v" then [1; 2; 4; 8; 16; 32; 64; (* 128; 256 *)]
    else  Lst.range 8
*)
    [1; 8; 7; 6; 5; 4; 3; 2;]

  and nblocks, abst_name =
    if domain.kind = "tiles"
    then
      ([
	 (* 3360 nblocks, 0-tile, 1-tile and 2-tile. *)
(*
	 (16 * 15 * 14);
*)
	 (* Technically there aren't 123 nblocks, this abst pays
	    attentions to the 1-tile, 2-tile and 3-tile. *)
	 123;
       ], "ignore-tiles")
    else
      if domain.kind = "grid"
      then
	if domain.name = "grids" || domain.name = "grids_unit4"
	then ([ (* 1600; 2500; *) 6400; ], "course-grid")
	else ([ (* 10_000; *) 62_500; (* 250_000; *) ], "course-grid")
      else ([], "<none>")

  and max_exps =
    if domain.kind = "tiles"
    then [ 32; ]
    else [ 64; ]

  and min_exps =
    if domain.kind = "tiles" then [ 16; ]
    else if domain.kind = "grid" then [ 32; ]
    else []

  and weights =
    [1.0]
      (*
	if domain.kind = "grid" then [ 1.1; 1.2; 1.4; 1.8; 3.4 ]
	else if domain.kind = "tiles" then [ 1.4; 1.7; 2.0; 3.0; 5.0 ]
	else []
      *)

  and wt_sched =
    (* Jordan's weights (3.0 decrementing by 0.2). *)
    (*
      ["3,2.8,2.6,2.4,2.2,2,1.8,1.6,1.4,1.2,1"]
    (* Silvia's weights. *)
      [ "3,2,1.5,1.25,1"; ]

    *)
    (* ICAPS paper weights. *)
    [ "7.4,4.2,2.6,1.8,1.4,1.2,1.1,1.0";
      "4.2,2.6,1.8,1.4,1.2,1.1,1.05,1.0";
      "3.0,2.8,2.6,2.4,2.2,2.0,1.8,1.6,1.4,1.2,1.0";
      "5.0,4.8,4.6,4.4,4.2,4.0,3.8,3.6,3.4,3.2,3.0,2.8,2.6,2.4,2.2,2.0,1.8,1.6,1.4,1.2,1.0";
    ]
      (*
      (* Silvia's weight schedules -- from grid_search.cc in Silvia's ARA* code *)
	[ "10.0,5.0,3.0,2.0,1.0";
	"5.0,3.0,2.0,1.5,1.0";
	"3.0,2.0,1.5,1.25,1.0";
	"2.0,1.5,1.25,1.125,1.0";]
      *)

  and multipliers = [ 1; 2; 4; ] in

  let algtab = [
    (* (name:string * abstraction:bool * params:(string * (string * string) list) list) the
       [params] element is a list of tuples of strings (the command line
       arg passed to the search executable) and key=value tuple lists
       (for rdb).  *)
    ("astar", [("astar", [])], true);

    ("idastar", [("idastar", [])], true);

    ("kbfs", (List.map
		(fun t -> (sprintf "kbfs-%d" t), [("threads", string_of_int t)])
		threads), true);

    ("pastar", (List.map
		  (fun t -> (sprintf "pastar-%d" t), [("threads", string_of_int t)])
		  threads), true);

    ("awastar", (List.map
		   (fun w -> (sprintf "awastar-%f" w), [("wt", string_of_float w)])
		   weights), true);

    ("arastar", (List.map
		   (fun w -> (sprintf "arastar %s" w), [("wt-sched", w)])
		   wt_sched), true);

    ("lpastar", (List.map
		   (fun (w, t) ->
		      (sprintf "lpastar-%f-%d" w t),
		      [("wt", string_of_float w);
		       ("threads", string_of_int t);])
		   (Lst.cart_prod weights threads)), false);


    ("syncwastar", (List.map
		      (fun (w, t) ->
			 (sprintf "syncwastar-%d %s" t w),
			 [("wt-sched", w);
			  ("threads", string_of_int t);])
		      (Lst.cart_prod wt_sched threads)), true);

    ("multiastar", (List.map
		      (fun t -> (sprintf "multiastar-%d" t), [("threads", string_of_int t)])
		      threads), true);

    ("multiwastar", (List.map
		       (fun (w, t) ->
			  (sprintf "multiwastar-%f-%d" w t),
			  [("wt", string_of_float w);
			   ("threads", string_of_int t);])
		       (Lst.cart_prod weights threads)), true);

    ("wastardd", (List.map
		    (fun w -> (sprintf "wastardd-%f" w), [("wt", string_of_float w)])
		    weights), false);

    ("wastar", (List.map
		  (fun w -> (sprintf "wastar-%f" w), [("wt", string_of_float w)])
		  weights), false);

    ("optimistic", (List.map
		      (fun w -> (sprintf "optimistic-%f" w), [("wt", string_of_float w)])
		      weights), false);

    ("prastar", (List.map
		   (fun (t, n) ->
		      (sprintf "prastar-%d" t),
		      [("threads", string_of_int t);])
		   (Lst.cart_prod threads nblocks)), true);

    ("aprastar", (List.map
		    (fun (t, n) ->
		       (sprintf "aprastar-%d-%d" t n),
		       ("abstraction", abst_name) ::
			 [("threads", string_of_int t);
			  ("nblocks", string_of_int n)])
		    (Lst.cart_prod threads nblocks)), true);

    ("hdastar", (List.map
		   (fun (t, m) ->
		      (sprintf "hdastar-%d-%d" m t),
		      [("max-expansions", string_of_int m);
		       ("threads", string_of_int t);
		      ])
		   (Lst.cart_prod threads max_exps)), true);

    ("ahdastar", (List.map
		    (fun ((w, t),(m, n)) ->
		       (sprintf "ahdastar-%f-%d-%d-%d" w m t n),
		       ("abstraction", abst_name) ::
			 [("wt", string_of_float w);
			  ("max-expansions", string_of_int m);
			  ("threads", string_of_int t);
			  ("nblocks", string_of_int n)])
		    (Lst.cart_prod
		       (Lst.cart_prod weights threads)
		       (Lst.cart_prod max_exps nblocks))), true);

    ("ahdastar-syncsends", (List.map
			      (fun (t, n) ->
				 (sprintf "ahdastar-syncsends-%d-%d" t n),
				 ("abstraction", abst_name) ::
				   [ ("threads", string_of_int t);
				     ("nblocks", string_of_int n)])
			      (Lst.cart_prod threads nblocks)), true);

    ("ahdastar-syncrecvs", (List.map
			      (fun ((t, n), m)->
				 (sprintf "ahdastar-syncrecvs-%d-%d-%d" m t n),
				 ("abstraction", abst_name) ::
				   [
				     ("max-expansions", string_of_int m);
				     ("threads", string_of_int t);
				     ("nblocks", string_of_int n)])
			      (Lst.cart_prod
				 (Lst.cart_prod threads nblocks)
				 max_exps)), true);

    ("hdastar-syncrecvs", (List.map
			     (fun (t, m) ->
				(sprintf "hdastar-syncrecvs-%d-%d" m t),
				[
				  ("max-expansions", string_of_int m);
				  ("threads", string_of_int t);
				])
			     (Lst.cart_prod threads max_exps)), true);

    ("hdastar-syncsends", (List.map
			     (fun t ->
				(sprintf "hdastar-syncsends-%d" t),
				[
				  ("threads", string_of_int t);
				])
			     threads), true);

    ("wahdastar", (List.map
		     (fun ((w, m), (t, n)) ->
			(sprintf "wahdastar-%f-%d-%d-%d" w m t n),
			("abstraction", abst_name) ::
			  [("wt", string_of_float w);
			   ("max-expansions", string_of_int m);
			   ("threads", string_of_int t);
			   ("nblocks", string_of_int n)])
		     (Lst.cart_prod
			(Lst.cart_prod weights max_exps)
			(Lst.cart_prod threads nblocks))), false);

    ("wahdastardd", (List.map
		       (fun ((w, m), (t, n)) ->
			  (sprintf "wahdastardd-%f-%d-%d-%d" w m t n),
			  ("abstraction", abst_name) ::
			    [("wt", string_of_float w);
			     ("max-expansions", string_of_int m);
			     ("threads", string_of_int t);
			     ("nblocks", string_of_int n)])
		       (Lst.cart_prod
			  (Lst.cart_prod weights max_exps)
			  (Lst.cart_prod threads nblocks))), false);

    ("whdastar", (List.map
		    (fun ((w, m), t) ->
		       (sprintf "whdastar-%f-%d-%d" w m t),
		       ("abstraction", abst_name) ::
			 [("wt", string_of_float w);
			  ("max-expansions", string_of_int m);
			  ("threads", string_of_int t);])
		    (Lst.cart_prod
		       (Lst.cart_prod weights max_exps)
		       threads)), false);

    ("whdastardd", (List.map
		      (fun ((w, m), t) ->
			 (sprintf "whdastardd-%f-%d-%d" w m t),
			 ("abstraction", abst_name) ::
			   [("wt", string_of_float w);
			    ("max-expansions", string_of_int m);
			    ("threads", string_of_int t);])
		      (Lst.cart_prod
			 (Lst.cart_prod weights max_exps)
			 threads)), false);


    ("waprastar", (List.map
		     (fun ((w, t), n) ->
			(sprintf "waprastar-%f-%d-%d" w t n),
			("abstraction", abst_name) ::
			  [("wt", string_of_float w);
			   ("threads", string_of_int t);
			   ("nblocks", string_of_int n)])
		     (Lst.cart_prod (Lst.cart_prod weights threads) nblocks)), false);


    ("waprastardd", (List.map
		       (fun ((w, t), n) ->
			  (sprintf "waprastardd-%f-%d-%d" w t n),
			  ("abstraction", abst_name) ::
			    [("wt", string_of_float w);
			     ("threads", string_of_int t);
			     ("nblocks", string_of_int n)])
		       (Lst.cart_prod (Lst.cart_prod weights threads) nblocks)), false);

    ("psdd", (List.map
		(fun (t, n) ->
		   (sprintf "psdd-%d-%d" t n),
		   ("abstraction", abst_name) ::
		     [("threads", string_of_int t);
		      ("nblocks", string_of_int n)])
		(Lst.cart_prod threads nblocks)), true);

    ("dynpsdd", (List.map
		   (fun ((w, t), n) ->
		      (sprintf "dynpsdd-%f-%d-%d" w t n),
		      ("abstraction", abst_name) ::
			[("wt", string_of_float w);
			 ("threads", string_of_int t);
			 ("nblocks", string_of_int n)])
		   (Lst.cart_prod (Lst.cart_prod weights threads) nblocks)), true);

    ("bfpsdd", (List.map
		  (fun ((u, m), (t, n)) ->
		     (sprintf "bfpsdd-%d-%d-%d-%d" u m t n),
		     ("abstraction", abst_name) ::
		       [("multiplier", string_of_int u);
			("min-expansions", string_of_int m);
			("threads", string_of_int t);
			("nblocks", string_of_int n)])
		  (Lst.cart_prod
		     (Lst.cart_prod multipliers min_exps)
		     (Lst.cart_prod threads nblocks))), true);

    ("wbfpsdd", (List.map
		   (fun (w, ((u, m), (t, n))) ->
		      (sprintf "wbfpsdd-%f-%d-%d-%d-%d" w u m t n),
		      ("abstraction", abst_name) ::
			[("wt", string_of_float w);
			 ("multiplier", string_of_int u);
			 ("min-expansions", string_of_int m);
			 ("threads", string_of_int t);
			 ("nblocks", string_of_int n)])
		   (Lst.cart_prod
		      weights
		      (Lst.cart_prod
			 (Lst.cart_prod multipliers min_exps)
			 (Lst.cart_prod threads nblocks)))), false);

    ("wbfpsdddd", (List.map
		     (fun (w, ((u, m), (t, n))) ->
			(sprintf "wbfpsdddd-%f-%d-%d-%d-%d" w u m t n),
			("abstraction", abst_name) ::
			  [("wt", string_of_float w);
			   ("multiplier", string_of_int u);
			   ("min-expansions", string_of_int m);
			   ("threads", string_of_int t);
			   ("nblocks", string_of_int n)])
		     (Lst.cart_prod
			weights
			(Lst.cart_prod
			   (Lst.cart_prod multipliers min_exps)
			   (Lst.cart_prod threads nblocks)))), false);

    ("idpsdd", (List.map
		  (fun (t, n) ->
		     (sprintf "idpsdd-%d-%d" t n),
		     ("abstraction", abst_name) ::
		       [("threads", string_of_int t);
			("nblocks", string_of_int n)])
		  (Lst.cart_prod threads nblocks)), true);

    ("arpbnf", (List.map
		  (fun ((w, m), (t, n)) ->
		     (sprintf "arpbnf-%d-%d-%d %s" m t n w),
		     ("abstraction", abst_name) ::
		       [("wt-sched", w);
			("min-expansions", string_of_int m);
			("threads", string_of_int t);
			("nblocks", string_of_int n)])
		  (Lst.cart_prod
		     (Lst.cart_prod wt_sched min_exps)
		     (Lst.cart_prod threads nblocks))), true);

    ("pbnf", (List.map
		(fun ((w, m), (t, n)) ->
		   (sprintf "pbnf-%f-%d-%d-%d" w m t n),
		   ("abstraction", abst_name) ::
		     [("wt", string_of_float w);
		      ("min-expansions", string_of_int m);
		      ("threads", string_of_int t);
		      ("nblocks", string_of_int n)])
		(Lst.cart_prod
		   (Lst.cart_prod weights min_exps)
		   (Lst.cart_prod threads nblocks))), true);

    ("safepbnf", (List.map
		    (fun ((w, m), (t, n)) ->
		       (sprintf "safepbnf-%f-%d-%d-%d" w m t n),
		       ("abstraction", abst_name) ::
			 [("wt", string_of_float w);
			  ("min-expansions", string_of_int m);
			  ("threads", string_of_int t);
			  ("nblocks", string_of_int n)])
		    (Lst.cart_prod
		       (Lst.cart_prod weights min_exps)
		       (Lst.cart_prod threads nblocks))), true);

    ("opbnf", (List.map
		 (fun ((w, m), (t, n)) ->
		    (sprintf "opbnf-%f-%d-%d-%d" w m t n),
		    ("abstraction", abst_name) ::
		      [("wt", string_of_float w);
		       ("min-expansions", string_of_int m);
		       ("threads", string_of_int t);
		       ("nblocks", string_of_int n)])
		 (Lst.cart_prod
		    (Lst.cart_prod weights min_exps)
		    (Lst.cart_prod threads nblocks))), false);

    ("wpbnf", (List.map
		 (fun ((w, m), (t, n)) ->
		    (sprintf "wpbnf-%f-%d-%d-%d" w m t n),
		    ("abstraction", abst_name) ::
		      [("wt", string_of_float w);
		       ("min-expansions", string_of_int m);
		       ("threads", string_of_int t);
		       ("nblocks", string_of_int n)])
		 (Lst.cart_prod
		    (Lst.cart_prod weights min_exps)
		    (Lst.cart_prod threads nblocks))), false);

    ("wpbnfdd", (List.map
		   (fun ((w, m), (t, n)) ->
		      (sprintf "wpbnfdd-%f-%d-%d-%d" w m t n),
		      ("abstraction", abst_name) ::
			[("wt", string_of_float w);
			 ("min-expansions", string_of_int m);
			 ("threads", string_of_int t);
			 ("nblocks", string_of_int n)])
		   (Lst.cart_prod
		      (Lst.cart_prod weights min_exps)
		      (Lst.cart_prod threads nblocks))), false);
  ] in
    (fun name ->
       try
	 List.hd (List.filter (fun (n, _, _) -> n = name) algtab)
       with _ -> failwith (sprintf "Bad algorithm name: %s" name))

(*
  Local Variables:
  compile-command: "ocm"
  End:
*)
