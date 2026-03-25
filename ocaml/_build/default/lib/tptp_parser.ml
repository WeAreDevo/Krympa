open Printf
open Str

(* ==================== helpers ==================== *)

let is_proof_line line =
  Str.string_match (regexp "^[0-9]+\\.") line 0
  && String.contains line '['

let extract_line_id line =
  try
    let p = String.index line '.' in
    int_of_string (String.sub line 0 p)
  with _ -> -1

let extract_formula_from_line line =
  try
    let dot_pos = String.index line '.' in
    let after_dot =
      String.sub line (dot_pos + 1) (String.length line - dot_pos - 1)
      |> String.trim
    in
    let bracket_pos = String.rindex after_dot '[' in
    String.sub after_dot 0 bracket_pos |> String.trim
  with Not_found ->
    printf "[DEBUG] Failed to extract formula from line: %s\n%!" line;
    ""

let extract_last_bracket line =
  try
    let dot_pos = String.index line '.' in
    let after_dot =
      String.sub line (dot_pos + 1) (String.length line - dot_pos - 1)
      |> String.trim
    in
    let l = String.rindex after_dot '[' in
    let r = String.rindex after_dot ']' in
    String.sub after_dot l (r - l + 1)
  with Not_found -> ""

(* ==================== tag checks ==================== *)

let is_input_line line =
  let tag = extract_last_bracket line in
  string_match (regexp ".*input.*") tag 0

let is_real_inference_step line =
  let tag = extract_last_bracket line in
  string_match (regexp ".*demodulation.*") tag 0
  || string_match (regexp ".*superposition.*") tag 0
  || string_match (regexp ".*resolution.*") tag 0

let extract_negated_conjecture_id line =
  if string_match
       (regexp ".*negated conjecture \\([0-9]+\\).*")
       line 0
  then
    Some (int_of_string (matched_group 1 line))
  else
    None

(* ==================== pass 1: find conjecture ==================== *)

let find_conjecture_id filename =
  let ic = open_in filename in
  let rec loop () =
    match input_line ic with
    | line ->
        begin
          match extract_negated_conjecture_id line with
          | Some id ->
              close_in ic;
              Some id
          | None -> loop ()
        end
    | exception End_of_file ->
        close_in ic;
        None
  in
  loop ()

(* ==================== pass 2: parse axioms + lemmas ==================== *)

let read_axioms_and_lemmas_from_file filename =
  let conjecture_id = find_conjecture_id filename in
  let ic = open_in filename in

  let rec loop axioms lemmas =
    match input_line ic with
    | line when String.length line > 0 && line.[0] = '%' ->
        loop axioms lemmas

    | line ->
        if is_proof_line line then begin
          let id = extract_line_id line in
          let formula = extract_formula_from_line line in

          if is_input_line line then
            (* real axiom only if not conjecture *)
            if Some id <> conjecture_id then
              loop (formula :: axioms) lemmas
            else
              loop axioms lemmas

          else if is_real_inference_step line then
            loop axioms (formula :: lemmas)

          else
            loop axioms lemmas
        end else
          loop axioms lemmas

    | exception End_of_file ->
        close_in ic;
        (List.rev axioms, List.rev lemmas)
  in
  loop [] []
