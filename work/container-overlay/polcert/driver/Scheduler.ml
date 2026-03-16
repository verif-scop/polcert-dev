

(* let scheduler  *)
open Result
open Driveraux
(* open CPolIRs *)
open Camlcoq
open Filename
open Str  (* Required for regular expressions *)

(** scop to scop *)

(** TODO: specify dump scop file name in pluto*)
let run_pluto_scop flags inscop =
  let inscop_file = tmp_file ".scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [["pluto"; "--dumpscop"; "--readscop"]; flags; [inscop_file]]
  in
  (* print_string ((String.concat " " cmd) ^ "\n"); *)
  let stdout =  (tmp_file (".stdout")) in
  let exc = command ?stdout:(Some stdout) cmd in
  let read_outscop () =
    if Sys.file_exists outscop_file then
      OpenScopReader.read outscop_file
    else
      None
  in
  match read_outscop () with
  | Some outscop -> Okk outscop
  | None ->
      if exc <> 0 then (
        safe_remove outscop_file;
        Err
          (coqstring_of_camlstring
             (Printf.sprintf "scheduler failed with exit code %d" exc))
      ) else
        Err (coqstring_of_camlstring ("scheduler failed"))

let read_file path =
  let ic = open_in path in
  let buf = Buffer.create 4096 in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
      (try
         while true do
           Buffer.add_string buf (input_line ic);
           Buffer.add_char buf '\n'
         done
       with End_of_file -> ());
      Buffer.contents buf)

let run_pluto_bridge flags inscop =
  let inscop_file = tmp_file ".scop" in
  let stdout_file = tmp_file ".stdout" in
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [["pluto"; "--readscop"]; flags; [inscop_file]]
  in
  let exc = command ?stdout:(Some stdout_file) cmd in
  let output = read_file stdout_file in
  if exc = 0 then
    Okk output
  else
    Err
      (coqstring_of_camlstring
         (Printf.sprintf "ISS bridge export failed with exit code %d" exc))

let affine_only_flags =
  [
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar";
  ]

let tile_only_flags =
  [
    "--identity";
    "--tile";
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--nounrolljam";
    "--noparallel";
    "--rar";
  ]

let affine_with_iss_flags =
  ["--iss"] @ affine_only_flags

let iss_identity_bridge_flags =
  [
    "--iss";
    "--identity";
    "--dump-iss-bridge";
    "--silent";
  ]

let affine_only_scop_scheduler inscop =
  run_pluto_scop affine_only_flags inscop

let tile_only_scop_scheduler inscop =
  run_pluto_scop tile_only_flags inscop

let affine_only_scop_scheduler_with_iss inscop =
  run_pluto_scop affine_with_iss_flags inscop

let iss_identity_bridge_from_scop inscop =
  run_pluto_bridge iss_identity_bridge_flags inscop

let run_pluto_phase_pipeline inscop =
  match affine_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler midscop with
        | Err msg -> Err msg
        | Okk outscop -> Okk (midscop, outscop)
      end

let run_pluto_phase_pipeline_with_iss inscop =
  match affine_only_scop_scheduler_with_iss inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler midscop with
        | Err msg -> Err msg
        | Okk outscop -> Okk (midscop, outscop)
      end

let phase_scop_scheduler = run_pluto_phase_pipeline

let infer_tiling_witness_scops before_scop after_scop =
  try
    let witness =
      PlutoTilingValidator.extract_witness_from_scops
        ~before_path:"mid_affine"
        ~after_path:"after_tiled"
        before_scop
        after_scop
    in
    Okk (PhaseTiling.convert_witness witness)
  with
  | PlutoTilingValidator.ValidationError msg ->
      Err (coqstring_of_camlstring msg)
  | exn ->
      Err (coqstring_of_camlstring (Printexc.to_string exn))

let scheduler' = affine_only_scop_scheduler


let find_and_extract_time filename =
  let ic = open_in filename in
  let rec process_lines () =
    try
      let line = input_line ic in
      let regex = regexp "\\[pluto\\] Auto-transformation time: \\([0-9.]+\\)s" in
      if string_match regex line 0 then begin
        let time_str = matched_group 1 line in
        let time_float = float_of_string time_str in
        close_in ic;
        time_float
      end else
        process_lines ()
    with
      End_of_file -> close_in ic; max_float
  in
  process_lines ()


(* also return the autoscheduling time, in pluto's stdout, "Auto-transformation time" *)
let invoke_pluto testname =
  let inscop_file = testname ^ ".beforescheduling.scop" in
  let outscop_file = testname ^ ".afterscheduling.scop" in
  let cmd = List.concat [
    ["pluto";
    "--dumpscop";
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";     
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar"];
    [testname ^ ".c"]
  ] in
  let stdout =  (tmp_file ("." ^ testname ^ ".stdout")) in
  print_string ("\027[90mInfo\027[0m: Executing \"" ^ (String.concat " " cmd) ^ "\"\n");
  let exc = command ?stdout:(Some stdout) cmd in
  if exc <> 0 then (
    command_error "invoke pluto failed" exc;)
  else 
    (* [pluto] Auto-transformation time: 0.001530s *)
    let runtime = find_and_extract_time stdout in
    Printf.printf "\027[90mInfo\027[0m: Invoke pluto succeed, with auto-transformation time %fs\n" runtime;
    print_string ("\027[90mInfo\027[0m: Reading " ^ (inscop_file) ^ " ...\n");
    match OpenScopReader.read inscop_file with 
    | Some inscop -> 
      print_string ("\027[90mInfo\027[0m: Read " ^ (inscop_file) ^ " successfully\n");
      (match OpenScopReader.read outscop_file with 
      | Some outscop ->
        print_string ("\027[90mInfo\027[0m: Read " ^ (outscop_file) ^ " successfully\n");
        Okk (inscop, outscop, runtime)
      | None -> Err (coqstring_of_camlstring ("invoke pluto failed"))
      )
    | None -> Err (coqstring_of_camlstring ("invoke pluto failed")) 
    
  (* match OpenScopReader.read inscop_file with
  | Some outscop -> Okk outscop
  | None -> Err (coqstring_of_camlstring ("cannot read " ^ inscop_file ^ "\n")) *)

(* let scheduler' cpol =
  let inscop = CPolIRs.PolyLang.to_openscop cpol in
  let inscop_file = tmp_file ".scop" in
  let outscop_file = tmp_file ".scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  match OpenScopReader.read inscop_file with
  | Some outscop -> CPolIRs.PolyLang.from_openscop cpol outscop
  | None -> Err (coqstring_of_camlstring ("Error: cannot read " ^ inscop_file ^ "\n")) *)

let scop_scheduler inscop = scheduler' inscop;;
