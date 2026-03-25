open Printf
open Str
open Sys
open Unix

(* ==================== helpers ==================== *)

(* take first n elements of a list *)
let rec take n xs =
  if n <= 0 then []
  else
    match xs with
    | [] -> []
    | x :: xs' -> x :: take (n - 1) xs'

(* remove leading quantifiers ! [...] : *)
let strip_leading_quantifiers formula =
  let re = Str.regexp "^[ \t]*![ \t]*\\[[^]]*\\][ \t]*:" in
  Str.global_replace re "" formula

(* normalize variables: Xn -> X0,X1..., keep Yn as-is *)
let normalize_variables_with_Y formula =
  let tokens = Str.split (regexp "[^a-zA-Z0-9_]+") formula in
  let vars =
    List.filter
      (fun t -> Str.string_match (Str.regexp "^[XY][0-9]+$") t 0)
      tokens
  in
  let uniq_vars = List.sort_uniq compare vars in
  let mapping =
    List.mapi
      (fun i v ->
        if String.get v 0 = 'X' then (v, sprintf "X%d" i) else (v, v))
      uniq_vars
  in
  let replaced =
    List.fold_left
      (fun acc (oldv, newv) ->
        Str.global_replace
          (Str.regexp (sprintf "\\b%s\\b" oldv))
          newv acc)
      formula mapping
  in
  (List.map snd mapping, replaced)

(* normalize all variables (Xn and Yn) *)
let normalize_variables formula =
  let tokens = Str.split (regexp "[^a-zA-Z0-9_]+") formula in
  let vars =
    List.filter
      (fun t -> Str.string_match (Str.regexp "^[XY][0-9]+$") t 0)
      tokens
  in
  let uniq_vars = List.sort_uniq compare vars in
  let mapping = List.mapi (fun i v -> (v, sprintf "X%d" i)) uniq_vars in
  let replaced =
    List.fold_left
      (fun acc (oldv, newv) ->
        Str.global_replace
          (Str.regexp (sprintf "\\b%s\\b" oldv))
          newv acc)
      formula mapping
  in
  (List.map snd mapping, replaced)

(* wrap formula into fof(...) *)
let fof_entry name role formula =
  let formula_no_inner = strip_leading_quantifiers formula in
  let vars, norm_formula = normalize_variables formula_no_inner in
  let quant =
    if vars = [] then ""
    else sprintf "! [%s] :" (String.concat ", " vars)
  in
  sprintf
    "fof(%s, %s,\n    %s\n      (%s)\n)."
    name role quant norm_formula

(* emit all axioms *)
let axioms_to_fof axioms =
  List.mapi
    (fun i ax -> fof_entry (sprintf "a%d" (i + 1)) "axiom" ax)
    axioms

(* ==================== big-step mode ==================== *)

let generate_fof_file_big_step idx axioms lemma =
  let axiom_fofs = axioms_to_fof axioms in
  let formula =
    fof_entry (sprintf "conjecture_%04d" idx) "conjecture" lemma
  in
  let content = String.concat "\n\n" (axiom_fofs @ [formula]) in
  let output_dir = "../lemmas" in
  if not (file_exists output_dir && is_directory output_dir) then
    mkdir output_dir 0o755;
  let filename = sprintf "%s/big_step_lemma_%04d.p" output_dir idx in
  let oc = open_out filename in
  fprintf oc "%s\n" content;
  close_out oc

let generate_all_files_big_step axioms lemmas =
  List.iteri
    (fun i lemma ->
      try generate_fof_file_big_step (i + 1) axioms lemma
      with exn ->
        eprintf
          "[DEBUG] Failed to write big_step_lemma_%04d.p: %s\n%!"
          (i + 1) (Printexc.to_string exn))
    lemmas

(* ==================== small-step mode ==================== *)

let generate_fof_file_small_step idx axioms lemmas =
  let axiom_fofs = axioms_to_fof axioms in
  let lemma_fofs =
    List.mapi
      (fun j lemma ->
        if j = idx then
          fof_entry (sprintf "conjecture_%04d" (j + 1)) "conjecture" lemma
        else
          fof_entry (sprintf "lemma_%04d" (j + 1)) "lemma" lemma)
      (take (idx + 1) lemmas)
  in
  let content = String.concat "\n\n" (axiom_fofs @ lemma_fofs) in
  let output_dir = "../lemmas" in
  if not (file_exists output_dir && is_directory output_dir) then
    mkdir output_dir 0o755;
  let filename = sprintf "%s/small_step_lemma_%04d.p" output_dir (idx + 1) in
  let oc = open_out filename in
  fprintf oc "%s\n" content;
  close_out oc

let generate_all_files_small_step axioms lemmas =
  List.iteri
    (fun i _ ->
      try generate_fof_file_small_step i axioms lemmas
      with exn ->
        eprintf
          "[DEBUG] Failed to write small_step_lemma_%04d.p: %s\n%!"
          (i + 1) (Printexc.to_string exn))
    lemmas

(* ==================== abstracted mode ==================== *)

(* Replace a single repeated flat op(x,y) term consistently with Y0 *)
let abstract_formula_single_term formula =
  let re = Str.regexp "op(\\([^()]*\\),\\([^()]*\\))" in
  let rec collect pos acc =
    try
      ignore (Str.search_forward re formula pos);
      let s = Str.match_beginning () in
      let e = Str.match_end () in
      let term = String.sub formula s (e - s) in
      collect e (term :: acc)
    with Not_found -> List.rev acc
  in
  let matches = collect 0 [] in
  let term_to_replace =
    match
      List.find_opt
        (fun t -> List.length (List.filter (( = ) t) matches) > 1)
        matches
    with
    | Some t -> t
    | None -> (match matches with [] -> "" | t :: _ -> t)
  in
  if term_to_replace = "" then formula
  else
    Str.global_replace
      (Str.regexp_string term_to_replace)
      "Y0" formula

let fof_entry_abstract name role formula =
  let formula_no_inner = strip_leading_quantifiers formula in
  let abs = abstract_formula_single_term formula_no_inner in
  let vars, norm_formula = normalize_variables_with_Y abs in
  let quant =
    if vars = [] then ""
    else sprintf "! [%s] :" (String.concat ", " vars)
  in
  sprintf
    "fof(%s, %s,\n    %s\n      (%s)\n)."
    name role quant norm_formula

let generate_fof_file_abstracted idx axioms lemma =
  let axiom_fofs = axioms_to_fof axioms in
  let formula =
    fof_entry_abstract
      (sprintf "conjecture_%04d" idx)
      "conjecture" lemma
  in
  let content = String.concat "\n\n" (axiom_fofs @ [formula]) in
  let output_dir = "../lemmas" in
  if not (file_exists output_dir && is_directory output_dir) then
    mkdir output_dir 0o755;
  let filename = sprintf "%s/abstracted_lemma_%04d.p" output_dir idx in
  let oc = open_out filename in
  fprintf oc "%s\n" content;
  close_out oc

let generate_all_files_abstracted axioms lemmas =
  List.iteri
    (fun i lemma ->
      try generate_fof_file_abstracted (i + 1) axioms lemma
      with exn ->
        eprintf
          "[DEBUG] Failed to write abstracted_lemma_%04d.p: %s\n%!"
          (i + 1) (Printexc.to_string exn))
    lemmas
