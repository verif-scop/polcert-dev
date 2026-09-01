module CLoop = CTypedLoopSamples.Loop
module CInstr = CPolIRs.CPolIRs.Instr
module CParallel = ParallelPolOpt.ParallelPolOpt (CPolIRs.CPolIRs)
module PLoop = CParallel.ParallelCodegenCore.ParallelLoop

let indent level = String.make (2 * level) ' '
let nat n = Camlcoq.Nat.to_int n
let z value = Camlcoq.Z.to_string value

let nth_or values index fallback =
  try List.nth values index with _ -> fallback

let slot values index =
  match List.nth_opt values (nat index) with
  | Some value -> value
  | None -> failwith (Printf.sprintf "instruction slot %d is out of range" (nat index))

let rec loop_expr env = function
  | CLoop.Constant value -> z value
  | CLoop.Var index -> nth_or env (nat index) (Printf.sprintf "v%d" (nat index))
  | CLoop.Sum (left, right) ->
      Printf.sprintf "(%s + %s)" (loop_expr env left) (loop_expr env right)
  | CLoop.Mult (factor, expr) ->
      Printf.sprintf "(%s * %s)" (z factor) (loop_expr env expr)
  | CLoop.Div (expr, divisor) ->
      Printf.sprintf "(%s / %s)" (loop_expr env expr) (z divisor)
  | CLoop.Mod (expr, divisor) ->
      Printf.sprintf "(%s %% %s)" (loop_expr env expr) (z divisor)
  | CLoop.Max (left, right) ->
      Printf.sprintf "max(%s, %s)" (loop_expr env left) (loop_expr env right)
  | CLoop.Min (left, right) ->
      Printf.sprintf "min(%s, %s)" (loop_expr env left) (loop_expr env right)

let rec parallel_expr env = function
  | PLoop.BaseLoop.Constant value -> z value
  | PLoop.BaseLoop.Var index ->
      nth_or env (nat index) (Printf.sprintf "v%d" (nat index))
  | PLoop.BaseLoop.Sum (left, right) ->
      Printf.sprintf "(%s + %s)"
        (parallel_expr env left) (parallel_expr env right)
  | PLoop.BaseLoop.Mult (factor, expr) ->
      Printf.sprintf "(%s * %s)" (z factor) (parallel_expr env expr)
  | PLoop.BaseLoop.Div (expr, divisor) ->
      Printf.sprintf "(%s / %s)" (parallel_expr env expr) (z divisor)
  | PLoop.BaseLoop.Mod (expr, divisor) ->
      Printf.sprintf "(%s %% %s)" (parallel_expr env expr) (z divisor)
  | PLoop.BaseLoop.Max (left, right) ->
      Printf.sprintf "max(%s, %s)"
        (parallel_expr env left) (parallel_expr env right)
  | PLoop.BaseLoop.Min (left, right) ->
      Printf.sprintf "min(%s, %s)"
        (parallel_expr env left) (parallel_expr env right)

let name id = Camlcoq.extern_atom id

let unary op value =
  match op with
  | Cop.Oneg -> Printf.sprintf "(-%s)" value
  | Cop.Onotbool -> Printf.sprintf "(!%s)" value
  | Cop.Onotint -> Printf.sprintf "(~%s)" value
  | Cop.Oabsfloat -> Printf.sprintf "abs(%s)" value

let binary op left right =
  let symbol =
    match op with
    | Cop.Oadd -> "+"
    | Cop.Osub -> "-"
    | Cop.Omul -> "*"
    | Cop.Odiv -> "/"
    | Cop.Omod -> "%"
    | Cop.Oand -> "&"
    | Cop.Oor -> "|"
    | Cop.Oxor -> "^"
    | Cop.Oshl -> "<<"
    | Cop.Oshr -> ">>"
    | Cop.Oeq -> "=="
    | Cop.One -> "!="
    | Cop.Olt -> "<"
    | Cop.Ogt -> ">"
    | Cop.Ole -> "<="
    | Cop.Oge -> ">="
  in
  Printf.sprintf "(%s %s %s)" left symbol right

let rec ma_expr render_slot slots = function
  | CInstr.MAval value -> z value
  | CInstr.MAvarz index ->
      render_slot (slot slots index)
  | CInstr.MAunop (op, expr) -> unary op (ma_expr render_slot slots expr)
  | CInstr.MAbinop (op, left, right) ->
      binary op (ma_expr render_slot slots left) (ma_expr render_slot slots right)

let ma_exprs render_slot slots values =
  let rec collect = function
    | CInstr.MAsingleton value -> [ma_expr render_slot slots value]
    | CInstr.MAcons (value, rest) ->
        ma_expr render_slot slots value :: collect rest
  in
  collect values

let access render_slot slots = function
  | CInstr.Avar id -> name id
  | CInstr.Aarr (id, indices) ->
      List.fold_left
        (fun text index -> text ^ "[" ^ index ^ "]")
        (name id) (ma_exprs render_slot slots indices)

let rec instr_expr render_slot slots = function
  | CInstr.Eval (Values.Vint value) -> z (Integers.Int.signed value)
  | CInstr.Eval _ -> "<constant>"
  | CInstr.Evarz index ->
      render_slot (slot slots index)
  | CInstr.Eaccess item -> access render_slot slots item
  | CInstr.Eunop (op, expr) -> unary op (instr_expr render_slot slots expr)
  | CInstr.Ebinop (op, left, right) ->
      binary op
        (instr_expr render_slot slots left)
        (instr_expr render_slot slots right)

let instruction render_slot slots = function
  | CInstr.Iskip -> "skip;"
  | CInstr.Iassign (target, value) ->
      Printf.sprintf "%s = %s;"
        (access render_slot slots target)
        (instr_expr render_slot slots value)

let rec loop_test env = function
  | CLoop.LE (left, right) ->
      Printf.sprintf "%s <= %s" (loop_expr env left) (loop_expr env right)
  | CLoop.EQ (left, right) ->
      Printf.sprintf "%s == %s" (loop_expr env left) (loop_expr env right)
  | CLoop.And (left, right) ->
      Printf.sprintf "(%s && %s)" (loop_test env left) (loop_test env right)
  | CLoop.Or (left, right) ->
      Printf.sprintf "(%s || %s)" (loop_test env left) (loop_test env right)
  | CLoop.Not test -> Printf.sprintf "!(%s)" (loop_test env test)
  | CLoop.TConstantTest value -> string_of_bool value

let rec parallel_test env = function
  | PLoop.BaseLoop.LE (left, right) ->
      Printf.sprintf "%s <= %s"
        (parallel_expr env left) (parallel_expr env right)
  | PLoop.BaseLoop.EQ (left, right) ->
      Printf.sprintf "%s == %s"
        (parallel_expr env left) (parallel_expr env right)
  | PLoop.BaseLoop.And (left, right) ->
      Printf.sprintf "(%s && %s)"
        (parallel_test env left) (parallel_test env right)
  | PLoop.BaseLoop.Or (left, right) ->
      Printf.sprintf "(%s || %s)"
        (parallel_test env left) (parallel_test env right)
  | PLoop.BaseLoop.Not test -> Printf.sprintf "!(%s)" (parallel_test env test)
  | PLoop.BaseLoop.TConstantTest value -> string_of_bool value

let rec loop_list = function
  | CLoop.SNil -> []
  | CLoop.SCons (head, tail) -> head :: loop_list tail

let rec parallel_list = function
  | PLoop.SNil -> []
  | PLoop.SCons (head, tail) -> head :: parallel_list tail

let fresh env depth =
  let rec choose index =
    let candidate = Printf.sprintf "i%d" (depth + index) in
    if List.mem candidate env then choose (index + 1) else candidate
  in
  choose 0

let rec loop_lines env depth level = function
  | CLoop.Loop (lower, upper, body) ->
      let iterator = fresh env depth in
      let header = Printf.sprintf "%sfor %s in range(%s, %s) {"
        (indent level) iterator (loop_expr env lower) (loop_expr env upper)
      in
      header :: loop_lines (iterator :: env) (depth + 1) (level + 1) body
      @ [indent level ^ "}"]
  | CLoop.Instr (instr, slots) ->
      [indent level ^ instruction (loop_expr env) slots instr]
  | CLoop.Seq statements ->
      List.concat (List.map (loop_lines env depth level) (loop_list statements))
  | CLoop.Guard (test, body) ->
      (Printf.sprintf "%sif (%s) {" (indent level) (loop_test env test))
      :: loop_lines env depth (level + 1) body @ [indent level ^ "}"]

let rec parallel_lines env depth level = function
  | PLoop.Loop (mode, _, lower, upper, body) ->
      let iterator = fresh env depth in
      let keyword =
        match mode with
        | PLoop.SeqMode -> "for"
        | PLoop.ParMode -> "parallel for"
        | PLoop.VecMode -> "innermost parallel for"
      in
      let header = Printf.sprintf "%s%s %s in range(%s, %s) {"
        (indent level) keyword iterator
        (parallel_expr env lower) (parallel_expr env upper)
      in
      header :: parallel_lines (iterator :: env) (depth + 1) (level + 1) body
      @ [indent level ^ "}"]
  | PLoop.Instr (instr, slots) ->
      [indent level ^ instruction (parallel_expr env) slots instr]
  | PLoop.Seq statements ->
      List.concat
        (List.map (parallel_lines env depth level) (parallel_list statements))
  | PLoop.Guard (test, body) ->
      (Printf.sprintf "%sif (%s) {" (indent level) (parallel_test env test))
      :: parallel_lines env depth (level + 1) body @ [indent level ^ "}"]

let loop (((statement, parameters), _) : CLoop.t) =
  let names = List.map name parameters in
  String.concat "\n"
    ((match names with
      | [] -> []
      | _ -> ["context(" ^ String.concat ", " names ^ ");"; ""])
     @ loop_lines (List.rev names) 0 0 statement)
  ^ "\n"

let parallel (((statement, parameters), _) : PLoop.t) =
  let names = List.map name parameters in
  String.concat "\n"
    ((match names with
      | [] -> []
      | _ -> ["context(" ^ String.concat ", " names ^ ");"; ""])
     @ parallel_lines (List.rev names) 0 0 statement)
  ^ "\n"

let output_root () =
  match Sys.getenv_opt "POLCERT_TYPED_PROGRAM_OUTPUT" with
  | Some path -> path
  | None -> failwith "POLCERT_TYPED_PROGRAM_OUTPUT is not set"

let write case filename text =
  let directory = Filename.concat (output_root ()) case in
  if not (Sys.file_exists directory) then Unix.mkdir directory 0o755;
  let channel = open_out (Filename.concat directory filename) in
  output_string channel text;
  close_out channel

let capture_loop case before after =
  write case "before.loop" (loop before);
  write case "after.loop" (loop after)

let capture_parallel case before after =
  write case "before.loop" (loop before);
  write case "after.loop" (parallel after)
