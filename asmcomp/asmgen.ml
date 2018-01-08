(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* From lambda to assembly code *)

[@@@ocaml.warning "+a-4-9-40-41-42"]

open Format
open Config
open Clflags
open Misc
open Cmm

type error = Assembler_error of string

exception Error of error

let liveness ppf phrase =
  Liveness.fundecl ppf phrase; phrase

let dump_if ppf flag message phrase =
  if !flag then Printmach.phase message ppf phrase

let pass_dump_if ppf flag message phrase =
  dump_if ppf flag message phrase; phrase

let pass_dump_linear_if ppf flag message phrase =
  if !flag then fprintf ppf "*** %s@.%a@." message Printlinear.fundecl phrase;
  phrase

let flambda_raw_clambda_dump_if ppf
      ({ Flambda_to_clambda. expr = ulambda; preallocated_blocks = _;
        structured_constants; exported = _; } as input) =
  if !dump_rawclambda then
    begin
      Format.fprintf ppf "@.clambda (before Un_anf):@.";
      Printclambda.clambda ppf ulambda;
      Symbol.Map.iter (fun sym cst ->
          Format.fprintf ppf "%a:@ %a@."
            Symbol.print sym
            Printclambda.structured_constant cst)
        structured_constants
    end;
  if !dump_cmm then Format.fprintf ppf "@.cmm:@.";
  input

type clambda_and_constants =
  Clambda.ulambda *
  Clambda.preallocated_block list *
  Clambda.preallocated_constant list

let raw_clambda_dump_if ppf
      ((ulambda, _, structured_constants):clambda_and_constants) =
  if !dump_rawclambda || !dump_clambda then
    begin
      Format.fprintf ppf "@.clambda:@.";
      Printclambda.clambda ppf ulambda;
      List.iter (fun {Clambda.symbol; definition} ->
          Format.fprintf ppf "%s:@ %a@."
            symbol
            Printclambda.structured_constant definition)
        structured_constants
    end;
  if !dump_cmm then Format.fprintf ppf "@.cmm:@."

let rec regalloc ppf round fd =
  if round > 50 then
    fatal_error(fd.Mach.fun_name ^
                ": function too complex, cannot complete register allocation");
  dump_if ppf dump_live "Liveness analysis" fd;
  if !use_linscan then begin
    (* Linear Scan *)
    Interval.build_intervals fd;
    if !dump_interval then Printmach.intervals ppf ();
    Linscan.allocate_registers()
  end else begin
    (* Graph Coloring *)
    Interf.build_graph fd;
    if !dump_interf then Printmach.interferences ppf ();
    if !dump_prefer then Printmach.preferences ppf ();
    Coloring.allocate_registers()
  end;
  dump_if ppf dump_regalloc "After register allocation" fd;
  let (newfd, redo_regalloc) = Reload.fundecl fd in
  dump_if ppf dump_reload "After insertion of reloading code" newfd;
  if redo_regalloc then begin
    Reg.reinit(); Liveness.fundecl ppf newfd; regalloc ppf (round + 1) newfd
  end else newfd

(* Begin: Polling efficiently on stock hardware - Marc Feeley *)

(* Terminology: four type of branches
   1. Local (inside a procedure, possibily conditional) branches
   2. Reductions = tail calls to procedures
   3. Subproblems = non-tail calls to procedures
   4. Returns (from a procedure call) *)

(* max number of "instructions" generated without an intervening poll *)
let l_max = 90

(* grace at entry *)
let e = l_max / 6

(* largest admissible delta at a reduction call *)
let r = e

(* A poll is just a 0-byte allocation to trigger all the behaviour an allocation entails
 * Especially important for multicore, numerical applications. *)
let add_poll e =
  let dbg, _args = Debuginfo.none, [Cconst_int 1] in
  (* Stolen from cmmgen.ml for 0-sized float-arrays *)
  let block_header tag sz = Nativeint.(add (shift_left (of_int sz) 10) (of_int tag)) in
  Csequence (Cop(Calloc, Cblockheader(block_header 0 0, dbg) :: [], dbg), e)

let insert_poll = 

  (* Is/should this reset on every call? *)
  let delta = ref (l_max - e) in

  (* Right to left evaluation? Unless the list is already reversed? *)
  let rec insert_polls exps =
    let rec loop acc = function
      | [] -> acc
      | (exp :: exps) -> let exp = non_branch exp in loop (exp :: acc) exps in
    loop [] (List.rev exps)

  (* Non-branching instructions *)
  and non_branch exp =
    let exp = insert_poll exp in
    if !delta >= l_max - 1 then
      (delta := 1; add_poll exp)
    else 
      (delta := !delta + 1; exp)

  and insert_poll =

    function

    | Cconst_int _     | Cconst_natint _     | Cconst_float _ | Cconst_symbol _
    | Cconst_pointer _ | Cconst_natpointer _ | Cblockheader _ | Cvar _  as exp ->
        if !delta >= l_max - 1 then
          (delta := 1; add_poll exp)
        else
          (delta := !delta + 1; exp)

    | Clet (id, exp1, exp2) ->
        (* Don't poll when an address is being computed, otherwise bad GC root (emit.mlp) *)
        begin match exp1 with
        | Cop(Cadda, _, _) -> (delta := !delta + 1; Clet (id, exp1, insert_poll exp2))
        | _ -> let exp1 = non_branch exp1 in Clet(id, exp1, insert_poll exp2)
        end

    | Cassign (id, exp) -> Cassign (id, insert_poll exp)
    | Ctuple exps -> Ctuple (insert_polls exps)
    | Csequence (exp1, exp2) -> let exp1 = non_branch exp1 in Csequence (exp1, insert_poll exp2)

    (* Branching *)
    | Cifthenelse (exp1, exp2, exp3) ->
        let exp1 = insert_poll exp1 in
        let delta1 = !delta in
        let exp2 = insert_poll exp2 in
        let delta2 = !delta in
        delta := delta1;
        let exp3 = insert_poll exp3 in
        delta := max delta2 !delta;
        Cifthenelse(exp1,exp2,exp3)

    | Cswitch (exp, int_arr, exp_arr, debug) ->
        let exp = insert_poll exp in
        let delta' = !delta in
        let max_delta = ref delta' in
        for i = 0 to Array.length exp_arr - 1 do
          Array.set exp_arr i (insert_poll (exp_arr.(i)));
          max_delta := max !max_delta !delta;
          delta := delta'
        done;
        delta := !max_delta;
        Cswitch (exp, int_arr, exp_arr, debug)

    | Ctrywith (exp1, id, exp2) ->
        let exp1 = insert_poll exp1 in
        let delta1 = !delta in
        (* Can't make any assumptions so reset *)
        delta := l_max - e;
        let exp2 = insert_poll exp2 in
        delta := max delta1 !delta;
        Ctrywith (exp1, id, exp2)

    (* Reductions/tail-calls (treating loops as such) *)
    | Cloop exp ->
        let delta' = !delta in
        delta := l_max - e;
        let exp = insert_poll exp in
        delta := delta';
        if !delta >= r then add_poll (Cloop exp) else Cloop exp

    (* Ccatch could be arbitrary control flow so no assumptions/resetting *)
    (* Continuations fall through to subsequent so delta is max of them all..? *)
    | Ccatch (rec_flag, int_id_exps, exp) ->
        let exp = non_branch exp in
        let max_delta = ref !delta in
        let rec loop = function
          | [] -> []
          | (int, id, exp) :: int_id_exps ->
              delta := l_max - e;
              let exp = insert_poll exp in
              max_delta := max !max_delta !delta;
              (int, id, exp) :: loop int_id_exps in
        let int_id_exps = loop int_id_exps in
        delta := !max_delta;
        Ccatch (rec_flag, int_id_exps, exp)

    (* Procedure return (assuming Cexit is that, couldn't understand selectgen.ml) *)
    (* Also assuming there are always interrupts between block entry and this point *)
    | Cexit (int, exps) ->
        let exps = insert_polls exps in
        if !delta >= e + r then
          add_poll (Cexit (int, exps))
        else
          Cexit (int,exps)

    | Cop (operation, exps, debug) -> cop_poll operation exps debug

  and cop_poll op exps debug = 

    (* Function calls *)
    match op with
    | Capply _ ->
        let exps = insert_polls exps in
        if !delta >= l_max - e then
          (delta := e + r;
           add_poll (Cop (op, exps, debug)))
        else 
          (delta := e + (max !delta r);
           Cop(op, exps, debug))

    (* Don't poll when an address is being computed, otherwise bad GC root (emit.mlp) *)
    | Cload _ | Cstore _ ->
        begin match exps with
        | [Cop(Cadda, _, _)] ->
            (delta := !delta + 1; Cop (op, exps, debug))
        | _ ->
            let exps = insert_polls exps in
            (delta := !delta + 1; Cop (op, exps, debug))
        end

    (* A poll can't do anything about a Cextcall messing up *)
    | Cextcall _ | Calloc | Caddi | Csubi | Cmuli | Cmulhi | Cdivi | Cmodi
    | Cand | Cor | Cxor | Clsl | Clsr | Casr | Ccmpi _
    | Caddv (* pointer addition that produces a [Val] (well-formed Caml value) *)
    | Cadda (* pointer addition that produces a [Addr] (derived heap pointer) *)
    | Ccmpa _ | Cnegf | Cabsf | Caddf | Csubf | Cmulf | Cdivf | Cfloatofint | Cintoffloat
    | Ccmpf _ | Craise _ | Ccheckbound ->
        let exps = insert_polls exps in
        (delta := !delta + 1; Cop (op, exps, debug))

  in fun x -> (delta := l_max - e; insert_poll x)

(* End: Polling efficiently on stock hardware - Marc Feeley *)

let (++) x f = f x

let compile_fundecl (ppf : formatter) fd_cmm =
  Proc.init ();
  Reg.reset();
  fd_cmm
  ++ Profile.record ~accumulate:true "insert_poll"
    (fun ({fun_body} as fundecl) -> {fundecl with fun_body = insert_poll fun_body})
  ++ Profile.record ~accumulate:true "selection" Selection.fundecl
  ++ pass_dump_if ppf dump_selection "After instruction selection"
  ++ Profile.record ~accumulate:true "comballoc" Comballoc.fundecl
  ++ pass_dump_if ppf dump_combine "After allocation combining"
  ++ Profile.record ~accumulate:true "cse" CSE.fundecl
  ++ pass_dump_if ppf dump_cse "After CSE"
  ++ Profile.record ~accumulate:true "liveness" (liveness ppf)
  ++ Profile.record ~accumulate:true "deadcode" Deadcode.fundecl
  ++ pass_dump_if ppf dump_live "Liveness analysis"
  ++ Profile.record ~accumulate:true "spill" Spill.fundecl
  ++ Profile.record ~accumulate:true "liveness" (liveness ppf)
  ++ pass_dump_if ppf dump_spill "After spilling"
  ++ Profile.record ~accumulate:true "split" Split.fundecl
  ++ pass_dump_if ppf dump_split "After live range splitting"
  ++ Profile.record ~accumulate:true "liveness" (liveness ppf)
  ++ Profile.record ~accumulate:true "regalloc" (regalloc ppf 1)
  ++ Profile.record ~accumulate:true "available_regs" Available_regs.fundecl
  ++ Profile.record ~accumulate:true "linearize" Linearize.fundecl
  ++ pass_dump_linear_if ppf dump_linear "Linearized code"
  ++ Profile.record ~accumulate:true "scheduling" Scheduling.fundecl
  ++ pass_dump_linear_if ppf dump_scheduling "After instruction scheduling"
  ++ Profile.record ~accumulate:true "emit" Emit.fundecl

let compile_phrase ppf p =
  if !dump_cmm then fprintf ppf "%a@." Printcmm.phrase p;
  match p with
  | Cfunction fd -> compile_fundecl ppf fd
  | Cdata dl -> Emit.data dl


(* For the native toplevel: generates generic functions unless
   they are already available in the process *)
let compile_genfuns ppf f =
  List.iter
    (function
       | (Cfunction {fun_name = name}) as ph when f name ->
           compile_phrase ppf ph
       | _ -> ())
    (Cmmgen.generic_functions true [Compilenv.current_unit_infos ()])

let compile_unit _output_prefix asm_filename keep_asm
      obj_filename gen =
  let create_asm = keep_asm || not !Emitaux.binary_backend_available in
  Emitaux.create_asm_file := create_asm;
  try
    if create_asm then Emitaux.output_channel := open_out asm_filename;
    begin try
      gen ();
      if create_asm then close_out !Emitaux.output_channel;
    with exn when create_asm ->
      close_out !Emitaux.output_channel;
      if not keep_asm then remove_file asm_filename;
      raise exn
    end;
    let assemble_result =
      Profile.record "assemble"
        (Proc.assemble_file asm_filename) obj_filename
    in
    if assemble_result <> 0
    then raise(Error(Assembler_error asm_filename));
    if create_asm && not keep_asm then remove_file asm_filename
  with exn ->
    remove_file obj_filename;
    raise exn

let set_export_info (ulambda, prealloc, structured_constants, export) =
  Compilenv.set_export_info export;
  (ulambda, prealloc, structured_constants)

let end_gen_implementation ?toplevel ppf
    (clambda:clambda_and_constants) =
  Emit.begin_assembly ();
  clambda
  ++ Profile.record "cmm" Cmmgen.compunit
  ++ Profile.record "compile_phrases" (List.iter (compile_phrase ppf))
  ++ (fun () -> ());
  (match toplevel with None -> () | Some f -> compile_genfuns ppf f);

  (* We add explicit references to external primitive symbols.  This
     is to ensure that the object files that define these symbols,
     when part of a C library, won't be discarded by the linker.
     This is important if a module that uses such a symbol is later
     dynlinked. *)

  compile_phrase ppf
    (Cmmgen.reference_symbols
       (List.filter (fun s -> s <> "" && s.[0] <> '%')
          (List.map Primitive.native_name !Translmod.primitive_declarations))
    );
  Emit.end_assembly ()

let flambda_gen_implementation ?toplevel ~backend ppf
    (program:Flambda.program) =
  let export = Build_export_info.build_export_info ~backend program in
  let (clambda, preallocated, constants) =
    Profile.record_call "backend" (fun () ->
      (program, export)
      ++ Flambda_to_clambda.convert
      ++ flambda_raw_clambda_dump_if ppf
      ++ (fun { Flambda_to_clambda. expr; preallocated_blocks;
                structured_constants; exported; } ->
             (* "init_code" following the name used in
                [Cmmgen.compunit_and_constants]. *)
           Un_anf.apply expr ~what:"init_code", preallocated_blocks,
           structured_constants, exported)
      ++ set_export_info)
  in
  let constants =
    List.map (fun (symbol, definition) ->
        { Clambda.symbol = Linkage_name.to_string (Symbol.label symbol);
          exported = true;
          definition })
      (Symbol.Map.bindings constants)
  in
  end_gen_implementation ?toplevel ppf
    (clambda, preallocated, constants)

let lambda_gen_implementation ?toplevel ppf
    (lambda:Lambda.program) =
  let clambda = Closure.intro lambda.main_module_block_size lambda.code in
  let preallocated_block =
    Clambda.{
      symbol = Compilenv.make_symbol None;
      exported = true;
      tag = 0;
      size = lambda.main_module_block_size;
    }
  in
  let clambda_and_constants =
    clambda, [preallocated_block], []
  in
  raw_clambda_dump_if ppf clambda_and_constants;
  end_gen_implementation ?toplevel ppf clambda_and_constants

let compile_implementation_gen ?toplevel prefixname
    ~required_globals ppf gen_implementation program =
  let asmfile =
    if !keep_asm_file || !Emitaux.binary_backend_available
    then prefixname ^ ext_asm
    else Filename.temp_file "camlasm" ext_asm
  in
  compile_unit prefixname asmfile !keep_asm_file
      (prefixname ^ ext_obj) (fun () ->
        Ident.Set.iter Compilenv.require_global required_globals;
        gen_implementation ?toplevel ppf program)

let compile_implementation_clambda ?toplevel prefixname
    ppf (program:Lambda.program) =
  compile_implementation_gen ?toplevel prefixname
    ~required_globals:program.Lambda.required_globals
    ppf lambda_gen_implementation program

let compile_implementation_flambda ?toplevel prefixname
    ~required_globals ~backend ppf (program:Flambda.program) =
  compile_implementation_gen ?toplevel prefixname
    ~required_globals ppf (flambda_gen_implementation ~backend) program

(* Error report *)

let report_error ppf = function
  | Assembler_error file ->
      fprintf ppf "Assembler error, input left in file %a"
        Location.print_filename file

let () =
  Location.register_error_of_exn
    (function
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
