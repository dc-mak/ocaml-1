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

(* Pretty-printing of C-- code *)

open Format
open Cmm

let rec_flag ppf = function
  | Nonrecursive -> ()
  | Recursive -> fprintf ppf " rec"

let machtype_component ppf = function
  | Val -> fprintf ppf "val"
  | Addr -> fprintf ppf "addr"
  | Int -> fprintf ppf "int"
  | Float -> fprintf ppf "float"

let machtype ppf mty =
  match Array.length mty with
  | 0 -> fprintf ppf "unit"
  | n -> machtype_component ppf mty.(0);
         for i = 1 to n-1 do
           fprintf ppf "*%a" machtype_component mty.(i)
         done

let comparison = function
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

let chunk = function
  | Byte_unsigned -> "unsigned int8"
  | Byte_signed -> "signed int8"
  | Sixteen_unsigned -> "unsigned int16"
  | Sixteen_signed -> "signed int16"
  | Thirtytwo_unsigned -> "unsigned int32"
  | Thirtytwo_signed -> "signed int32"
  | Word_int -> "int"
  | Word_val -> "val"
  | Single -> "float32"
  | Double -> "float64"
  | Double_u -> "float64u"

let raise_kind fmt = function
  | Raise_withtrace -> Format.fprintf fmt "raise_withtrace"
  | Raise_notrace -> Format.fprintf fmt "raise_notrace"

let operation d = function
  | Capply _ty -> "app" ^ Debuginfo.to_string d
  | Cextcall(lbl, _ty, _alloc, _) ->
      Printf.sprintf "extcall \"%s\"%s" lbl (Debuginfo.to_string d)
  | Cload (c, Asttypes.Immutable) -> Printf.sprintf "load %s" (chunk c)
  | Cload (c, Asttypes.Mutable) -> Printf.sprintf "load_mut %s" (chunk c)
  | Calloc -> "alloc" ^ Debuginfo.to_string d
  | Cstore (c, init) ->
    let init =
      match init with
      | Lambda.Heap_initialization -> "(heap-init)"
      | Lambda.Root_initialization -> "(root-init)"
      | Lambda.Assignment -> ""
    in
    Printf.sprintf "store %s%s" (chunk c) init
  | Caddi -> "+"
  | Csubi -> "-"
  | Cmuli -> "*"
  | Cmulhi -> "*h"
  | Cdivi -> "/"
  | Cmodi -> "mod"
  | Cand -> "and"
  | Cor -> "or"
  | Cxor -> "xor"
  | Clsl -> "<<"
  | Clsr -> ">>u"
  | Casr -> ">>s"
  | Ccmpi c -> comparison c
  | Caddv -> "+v"
  | Cadda -> "+a"
  | Ccmpa c -> Printf.sprintf "%sa" (comparison c)
  | Cnegf -> "~f"
  | Cabsf -> "absf"
  | Caddf -> "+f"
  | Csubf -> "-f"
  | Cmulf -> "*f"
  | Cdivf -> "/f"
  | Cfloatofint -> "floatofint"
  | Cintoffloat -> "intoffloat"
  | Ccmpf c -> Printf.sprintf "%sf" (comparison c)
  | Craise k -> Format.asprintf "%a%s" raise_kind k (Debuginfo.to_string d)
  | Ccheckbound -> "checkbound" ^ Debuginfo.to_string d

let rec expr ppf = function
  | Cconst_int n -> fprintf ppf "%i" n
  | Cconst_natint n ->
    fprintf ppf "%s" (Nativeint.to_string n)
  | Cblockheader(n, d) ->
    fprintf ppf "block-hdr(%s)%s"
      (Nativeint.to_string n) (Debuginfo.to_string d)
  | Cconst_float n -> fprintf ppf "%F" n
  | Cconst_symbol s -> fprintf ppf "\"%s\"" s
  | Cconst_pointer n -> fprintf ppf "%ia" n
  | Cconst_natpointer n -> fprintf ppf "%sa" (Nativeint.to_string n)
  | Cvar id -> Ident.print ppf id
  | Clet(id, def, (Clet(_, _, _) as body)) ->
      let print_binding id ppf def =
        fprintf ppf "@[<2>%a@ %a@]" Ident.print id expr def in
      let rec in_part ppf = function
        | Clet(id, def, body) ->
            fprintf ppf "@ %a" (print_binding id) def;
            in_part ppf body
        | exp -> exp in
      fprintf ppf "@[<2>(let@ @[<1>(%a" (print_binding id) def;
      let exp = in_part ppf body in
      fprintf ppf ")@]@ %a)@]" sequence exp
  | Clet(id, def, body) ->
     fprintf ppf
      "@[<2>(let@ @[<2>%a@ %a@]@ %a)@]"
      Ident.print id expr def sequence body
  | Cassign(id, exp) ->
      fprintf ppf "@[<2>(assign @[<2>%a@ %a@])@]" Ident.print id expr exp
  | Ctuple el ->
      let tuple ppf el =
       let first = ref true in
       List.iter
        (fun e ->
          if !first then first := false else fprintf ppf "@ ";
          expr ppf e)
        el in
      fprintf ppf "@[<1>[%a]@]" tuple el
  | Cop(op, el, dbg) ->
      fprintf ppf "@[<2>(%s" (operation dbg op);
      List.iter (fun e -> fprintf ppf "@ %a" expr e) el;
      begin match op with
      | Capply mty -> fprintf ppf "@ %a" machtype mty
      | Cextcall(_, mty, _, _) -> fprintf ppf "@ %a" machtype mty
      | _ -> ()
      end;
      fprintf ppf ")@]"
  | Csequence(e1, e2) ->
      fprintf ppf "@[<2>(seq@ %a@ %a)@]" sequence e1 sequence e2
  | Cifthenelse(e1, e2, e3) ->
      fprintf ppf "@[<2>(if@ %a@ %a@ %a)@]" expr e1 expr e2 expr e3
  | Cswitch(e1, index, cases, _dbg) ->
      let print_case i ppf =
        for j = 0 to Array.length index - 1 do
          if index.(j) = i then fprintf ppf "case %i:" j
        done in
      let print_cases ppf =
       for i = 0 to Array.length cases - 1 do
        fprintf ppf "@ @[<2>%t@ %a@]" (print_case i) sequence cases.(i)
       done in
      fprintf ppf "@[<v 0>@[<2>(switch@ %a@ @]%t)@]" expr e1 print_cases
  | Cloop e ->
      fprintf ppf "@[<2>(loop@ %a)@]" sequence e
  | Ccatch(flag, handlers, e1) ->
      let print_handler ppf (i, ids, e2) =
        fprintf ppf "(%d%a)@ %a"
          i
          (fun ppf ids ->
             List.iter
               (fun id -> fprintf ppf " %a" Ident.print id)
               ids) ids
          sequence e2
      in
      let print_handlers ppf l =
        List.iter (print_handler ppf) l
      in
      fprintf ppf
        "@[<2>(catch%a@ %a@;<1 -2>with%a)@]"
        rec_flag flag
        sequence e1
        print_handlers handlers
  | Cexit (i, el) ->
      fprintf ppf "@[<2>(exit %d" i;
      List.iter (fun e -> fprintf ppf "@ %a" expr e) el;
      fprintf ppf ")@]"
  | Ctrywith(e1, id, e2) ->
      fprintf ppf "@[<2>(try@ %a@;<1 -2>with@ %a@ %a)@]"
             sequence e1 Ident.print id sequence e2

and sequence ppf = function
  | Csequence(e1, e2) -> fprintf ppf "%a@ %a" sequence e1 sequence e2
  | e -> expression ppf e

and expression ppf e = fprintf ppf "%a" expr e

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
let fundecl ppf f =
  let print_cases ppf cases =
    let first = ref true in
    List.iter
     (fun (id, ty) ->
       if !first then first := false else fprintf ppf "@ ";
       fprintf ppf "%a: %a" Ident.print id machtype ty)
     cases in
  fprintf ppf "@[<1>(function%s %s@;<1 4>@[<1>(%a)@]@ @[%a@])@]@."
         (Debuginfo.to_string f.fun_dbg) f.fun_name
         print_cases f.fun_args sequence (Csequence(f.fun_body, insert_poll f.fun_body))

let data_item ppf = function
  | Cdefine_symbol s -> fprintf ppf "\"%s\":" s
  | Cglobal_symbol s -> fprintf ppf "global \"%s\"" s
  | Cint8 n -> fprintf ppf "byte %i" n
  | Cint16 n -> fprintf ppf "int16 %i" n
  | Cint32 n -> fprintf ppf "int32 %s" (Nativeint.to_string n)
  | Cint n -> fprintf ppf "int %s" (Nativeint.to_string n)
  | Csingle f -> fprintf ppf "single %F" f
  | Cdouble f -> fprintf ppf "double %F" f
  | Csymbol_address s -> fprintf ppf "addr \"%s\"" s
  | Cstring s -> fprintf ppf "string \"%s\"" s
  | Cskip n -> fprintf ppf "skip %i" n
  | Calign n -> fprintf ppf "align %i" n

let data ppf dl =
  let items ppf = List.iter (fun d -> fprintf ppf "@ %a" data_item d) dl in
  fprintf ppf "@[<hv 1>(data%t)@]" items

let phrase ppf = function
  | Cfunction f -> fundecl ppf f
  | Cdata dl -> data ppf dl
