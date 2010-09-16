(**
   Info about domains.
*)

open Printf

type t = {
  name: string;
  kind: string;
  params: (string * string) list list;
}

let domaintab = [
  { name="korf";
    kind = "tiles";
    params = [
      (*
      [("model", "korf_easy"); ("rows", "4"); ("cols", "4");("runnum", "1")];
      *)
      [("model", "korf"); ("rows", "4"); ("cols", "4");];
    ];
  };
  { name="snlemons_easy";
    kind = "tiles";
    params = [
      [("model", "snlemons_easy"); ("rows", "4"); ("cols", "4");];
    ];
  };

  { name="korf_easy";
    kind = "tiles";
    params = [
      [("model", "korf_easy"); ("rows", "4"); ("cols", "4");("runnum", "1")];
    ];
  };

  { name="grids";
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params =
         (* Fix this to be 2 lists for each param set (prob wise). *)
	 [("prob", "0.35"); ("width", "2000"); ("height", "1200");]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Unit"); ("moves", "Four-way")];
	      [("costs", "Life"); ("moves", "Four-way")];
	      [("costs", "Unit"); ("moves", "Eight-way")];
	      [("costs", "Life"); ("moves", "Eight-way")];
	    ]);
  };
  { name="grids_unit4";
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params =
         (* Fix this to be 2 lists for each param set (prob wise). *)
	 [("prob", "0.35"); ("width", "2000"); ("height", "1200");]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Unit"); ("moves", "Four-way")];
	    ]);
  };
  { name="wgrids";
    (*
      Weighted searches don't perform well on life 8-way grids, so we
      leave them out.
    *)
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params =
         (* Fix this to be 2 lists for each param set (prob wise). *)
	 [("prob", "0.35"); ("width", "2000"); ("height", "1200");]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Unit"); ("moves", "Four-way")];
	      [("costs", "Life"); ("moves", "Four-way")];
	      [("costs", "Unit"); ("moves", "Eight-way")];
	    ]);
  };
  { name="5000_grids";
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params = [("width", "5000"); ("height", "5000")]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Unit"); ("moves", "Four-way"); ("prob", "0.35");];
	      [("costs", "Life"); ("moves", "Four-way"); ("prob", "0.35"); ];
	      [("costs", "Unit"); ("moves", "Eight-way"); ("prob", "0.45"); ];
	      [("costs", "Life"); ("moves", "Eight-way"); ("prob", "0.45"); ];
	    ]);
  };
  { name="5000_wgrids";
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params = [("width", "5000"); ("height", "5000")]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Unit"); ("moves", "Four-way"); ("prob", "0.35");];
	      [("costs", "Unit"); ("moves", "Eight-way"); ("prob", "0.45"); ];
	    ]);
  };
  { name="5000_grids_unit4";
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params = [("width", "5000"); ("height", "5000")]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Unit"); ("moves", "Four-way"); ("prob", "0.35");];
	    ]);
  };
  { name="5000_grids_life4";
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params = [("width", "5000"); ("height", "5000")]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Life"); ("moves", "Four-way"); ("prob", "0.35");];
	    ]);
  };
  { name="5000_grids_unit8";
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params = [("width", "5000"); ("height", "5000")]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Unit"); ("moves", "Eight-way"); ("prob", "0.45");];
	    ]);
  };
  { name="5000_grids_life8";
    kind = "grid";
    params =
      (let front_params =
	 [("obstacles", "uniform")]
       and back_params = [("width", "5000"); ("height", "5000")]
       in List.map
	    (fun l -> front_params @ l @ back_params)
	    [
	      [("costs", "Life"); ("moves", "Eight-way"); ("prob", "0.45");];
	    ]);
  };
]


(* Get a domain structure given the name *)
let by_name name =
  try
    List.hd (List.filter (fun elm -> elm.name = name) domaintab)
  with _ -> failwith (sprintf "Bad domain name: %s" name)

(*
  Local Variables:
  compile-command: "ocm"
  End:
*)
