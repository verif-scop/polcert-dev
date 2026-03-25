open Design_validator_core
open Tiling_core

type config = {
  scenario : string;
  json : bool;
}

let usage () =
  Printf.printf "usage: design_validator_prototype [--json] scenario.json\n"

let parse_args argv =
  let json = ref false in
  let positional = ref [] in
  let rec loop i =
    if i >= Array.length argv then ()
    else
      match argv.(i) with
      | "--json" ->
          json := true;
          loop (i + 1)
      | "-h" | "--help" ->
          usage ();
          exit 0
      | arg ->
          positional := !positional @ [ arg ];
          loop (i + 1)
  in
  loop 1;
  match !positional with
  | [ scenario ] -> { scenario; json = !json }
  | _ ->
      usage ();
      exit 1

let () =
  try
    let cfg = parse_args Sys.argv in
    let scenario = scenario_of_yojson (Yojson.Safe.from_file cfg.scenario) in
    let report = validate_scenario scenario in
    if cfg.json then
      Yojson.Safe.pretty_to_channel stdout (report_to_yojson report)
    else
      print_endline (render_report report);
    exit (if report.ok then 0 else 2)
  with
  | Validation_error msg ->
      if Array.exists (( = ) "--json") Sys.argv then
        Yojson.Safe.pretty_to_channel stdout (`Assoc [ ("ok", `Bool false); ("error", `String msg) ])
      else
        prerr_endline ("[design-validator] ERROR: " ^ msg);
      exit 1
  | Sys_error msg ->
      if Array.exists (( = ) "--json") Sys.argv then
        Yojson.Safe.pretty_to_channel stdout (`Assoc [ ("ok", `Bool false); ("error", `String msg) ])
      else
        prerr_endline ("[design-validator] ERROR: " ^ msg);
      exit 1
