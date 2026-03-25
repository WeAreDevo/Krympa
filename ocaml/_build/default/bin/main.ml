open Printf
open Ocaml

let () =
  if Array.length Sys.argv < 3 then begin
    prerr_endline "Usage: main <vampire_proof_file> <mode>";
    prerr_endline "  mode = big-step   -> axioms + lemma_i";
    prerr_endline "  mode = small-step -> axioms + lemmas 1..(i-1) + lemma_i";
    prerr_endline "  mode = abstracted -> axioms + lemma_i with nested op(...) replaced by variables";
    exit 1
  end;

  let filename = Sys.argv.(1) in
  let mode = Sys.argv.(2) in

  let (axioms, lemmas) =
    Tptp_parser.read_axioms_and_lemmas_from_file filename
  in

  printf "[INFO] Extracted %d axioms.\n%!" (List.length axioms);
  List.iter (fun ax -> printf "%s\n%!" ax) axioms;

  printf "[INFO] Extracted %d lemmas from the proof file.\n%!"
    (List.length lemmas);

  match mode with
  | "big-step" ->
      Lemma_extractor.generate_all_files_big_step axioms lemmas;
      printf "[INFO] Generated %d TPTP big-step .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | "small-step" ->
      Lemma_extractor.generate_all_files_small_step axioms lemmas;
      printf "[INFO] Generated %d TPTP small-step .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | "abstracted" ->
      Lemma_extractor.generate_all_files_abstracted axioms lemmas;
      printf "[INFO] Generated %d TPTP abstracted .p files in the lemmas directory.\n%!"
        (List.length lemmas)

  | _ ->
      eprintf "[ERROR] Unknown mode: %s (expected 'big-step', 'small-step', or 'abstracted')\n%!"
        mode;
      exit 1
