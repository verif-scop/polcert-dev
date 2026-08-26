open Tiling_core

type command =
  | Validate
  | Extract
  | Check

type config = {
  command : command;
  before : string;
  after : string;
  witness : string option;
  params : string list;
  check_bounded_coverage : bool;
  json : bool;
}

let default_config =
  {
    command = Validate;
    before = "";
    after = "";
    witness = None;
    params = [];
    check_bounded_coverage = false;
    json = false;
  }

let usage () =
  Printf.printf
    "usage: pluto_tiling_ocaml {validate,extract,check} [options] before.scop after.scop [witness.json]\n";
  Printf.printf "  --param NAME=VALUE\n";
  Printf.printf "  --check-bounded-coverage\n";
  Printf.printf "  --json\n"

let emit_json_error msg =
  Yojson.Safe.pretty_to_channel stdout (`Assoc [ ("ok", `Bool false); ("error", `String msg) ])

let parse_args argv =
  if Array.length argv < 2 then (usage (); exit 1);
  let command, start =
    match argv.(1) with
    | "validate" -> (Validate, 2)
    | "extract" -> (Extract, 2)
    | "check" -> (Check, 2)
    | "-h" | "--help" -> (usage (); exit 0)
    | _ -> (Validate, 1)
  in
  let rec loop i cfg positional =
    if i >= Array.length argv then (cfg, List.rev positional)
    else
      match argv.(i) with
      | "--param" ->
          if i + 1 >= Array.length argv then raise (Validation_error "--param expects NAME=VALUE");
          loop (i + 2) { cfg with params = cfg.params @ [ argv.(i + 1) ] } positional
      | "--check-bounded-coverage" -> loop (i + 1) { cfg with check_bounded_coverage = true } positional
      | "--json" -> loop (i + 1) { cfg with json = true } positional
      | "-h" | "--help" ->
          usage ();
          exit 0
      | arg -> loop (i + 1) cfg (arg :: positional)
  in
  let cfg, positional = loop start { default_config with command } [] in
  match (command, positional) with
  | Validate, [ before; after ] -> { cfg with before; after }
  | Extract, [ before; after ] -> { cfg with before; after }
  | Check, [ before; after; witness ] -> { cfg with before; after; witness = Some witness }
  | _ ->
      usage ();
      exit 1

let () =
  try
    let cfg = parse_args Sys.argv in
    (try
       match cfg.command with
       | Validate ->
           let report =
             validate_tiling cfg.before cfg.after (parse_param_assignments cfg.params) cfg.check_bounded_coverage
           in
           if cfg.json then
             Yojson.Safe.pretty_to_channel stdout (validation_report_to_yojson report)
           else print_endline (render_validation_report report);
           exit (if report.ok then 0 else 2)
       | Extract ->
           let witness = infer_tiling_witness cfg.before cfg.after in
           if cfg.json then Yojson.Safe.pretty_to_channel stdout (witness_to_yojson witness)
           else print_endline (render_tiling_witness witness);
           exit 0
       | Check ->
           let witness_path =
             match cfg.witness with Some path -> path | None -> raise (Validation_error "missing witness path")
           in
           let witness = witness_of_yojson (Yojson.Safe.from_file witness_path) in
           let report =
             check_tiling_witness cfg.before cfg.after witness (parse_param_assignments cfg.params)
               cfg.check_bounded_coverage
           in
           if cfg.json then
             Yojson.Safe.pretty_to_channel stdout (validation_report_to_yojson report)
           else print_endline (render_validation_report report);
           exit (if report.ok then 0 else 2)
     with
    | Validation_error msg ->
        if cfg.json then emit_json_error msg else prerr_endline ("[pluto-tiling-ocaml] ERROR: " ^ msg);
        exit 1
    | Sys_error msg ->
        if cfg.json then emit_json_error msg else prerr_endline ("[pluto-tiling-ocaml] ERROR: " ^ msg);
        exit 1)
  with
  | Validation_error msg ->
      prerr_endline ("[pluto-tiling-ocaml] ERROR: " ^ msg);
      exit 1
  | Sys_error msg ->
      prerr_endline ("[pluto-tiling-ocaml] ERROR: " ^ msg);
      exit 1
