use crate::alpha_match::formulas_match;
use crate::dag::*;
use crate::execution::{execution_mode, term_size_aware, ExecutionMode};
use crate::prover_wrapper::*;
use crate::run_vamp::run_vampire;
use crate::superpose::*;
use crate::utils::*;
use rayon::prelude::*;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

type RootEval = (
    usize,  // lemma_count
    usize,  // steps_total
    String, // root_lemma
    String, // best_history
    String, // annotated_proof
    String, // dag_text
    String, // lemmas_text
);

fn format_active_roots(active: &BTreeSet<String>) -> String {
    if active.is_empty() {
        "none".to_string()
    } else {
        active.iter().cloned().collect::<Vec<_>>().join(", ")
    }
}

fn is_small_step_lemma(name: &str) -> bool {
    name.starts_with("small_step_lemma_")
}

fn is_big_step_lemma(name: &str) -> bool {
    name.starts_with("big_step_lemma_")
}

fn is_abstracted_lemma(name: &str) -> bool {
    name.starts_with("abstracted_lemma_")
}

struct ActiveRootGuard<'a> {
    root: String,
    active_roots: &'a std::sync::Mutex<BTreeSet<String>>,
    total_roots: usize,
}

impl Drop for ActiveRootGuard<'_> {
    fn drop(&mut self) {
        if let Ok(mut active) = self.active_roots.lock() {
            active.remove(&self.root);
            crate::klog_info!(
                "[INFO] Arrival lemma finished: {} | active {}/{}: {}",
                self.root,
                active.len(),
                self.total_roots,
                format_active_roots(&active)
            );
        }
    }
}

/// Tries several candidate root lemmas and picks the best
pub fn try_minimize(
    input_file: &str,
    vampire_file: &str,
    summary_file: &str,
) -> Result<String, String> {
    let lemmas_dir = "../lemmas".to_string();
    let proofs_dir = "../proofs".to_string();
    let twee_proofs_dir = "../proofs/twee_tmp".to_string();
    let input_content = fs::read_to_string(input_file)
        .map_err(|e| format!("Failed to read input file {}: {}", input_file, e))?;

    let suffix = extract_suffix(input_file);
    let dag_with_suffix = format!("../output/dag_{}.txt", suffix);
    let lemmas_with_suffix = format!("../output/lemmas_{}.p", suffix);
    let proof_with_suffix = format!("../output/proof_{}.out", suffix);

    let summary_data: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(summary_file).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;

    let max_key = summary_data
        .as_object()
        .ok_or("summary.json should contain an object")?
        .keys()
        .filter_map(|k| k.parse::<u32>().ok())
        .max()
        .ok_or("summary.json is empty")?;

    let global_best = std::sync::Mutex::new(None::<RootEval>);

    // precompute lemmas
    let precomputed = precompute_lemmas(&proofs_dir, &lemmas_dir, &twee_proofs_dir)?;

    let mut offset = 0;
    let mut accepted = 0;
    let max_candidates = 5;

    // select root candidates first (serial), then evaluate them in parallel.
    let skolem_re = Regex::new(r"\bsK\d+\b").unwrap();
    let mut selected_roots: Vec<(String, String)> = Vec::new();
    while accepted < max_candidates && offset < max_key {
        let key = (max_key - offset).to_string();
        offset += 1;

        // check if key exists in summary_data
        let entry = match summary_data.get(&key) {
            Some(e) => e,
            None => {
                // key not found in summary, skipping.
                continue;
            }
        };

        let root_lemma = entry[0]
            .as_str()
            .ok_or("Bad summary.json format")?
            .to_string();

        let root_formula = load_lemma(&lemmas_dir, &root_lemma)
            .map_err(|_| format!("Missing lemma {}", root_lemma))?;

        if skolem_re.is_match(&root_formula) {
            crate::klog_debug!(
                "[DEBUG] Skipping root lemma {} due to Skolem constants in formula: {}",
                root_lemma,
                root_formula
            );
            // skipping lemma because it contains Skolem constants
            continue;
        }

        // valid root lemma
        accepted += 1;
        selected_roots.push((root_lemma, root_formula));
    }
    let selected_root_names = selected_roots
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>()
        .join(", ");
    let total_roots = selected_roots.len();
    let active_roots = std::sync::Mutex::new(BTreeSet::<String>::new());
    let mode = execution_mode();
    crate::klog_info!(
        "[INFO] Evaluating {} arrival candidates in {} mode: {}",
        total_roots,
        mode.as_str(),
        selected_root_names
    );

    let process_root = |(root_lemma, root_formula): &(String, String)| -> Result<(), String> {
        {
            let mut active = active_roots
                .lock()
                .map_err(|_| "Failed to lock active_roots".to_string())?;
            active.insert(root_lemma.clone());
            crate::klog_info!(
                "[INFO] Arrival lemma started: {} | active {}/{}: {}",
                root_lemma,
                active.len(),
                total_roots,
                format_active_roots(&active)
            );
        }
        let _active_guard = ActiveRootGuard {
            root: root_lemma.clone(),
            active_roots: &active_roots,
            total_roots,
        };
        crate::klog_debug!("[DEBUG] Root lemma {}", root_lemma);

        // build the minimal dag
        let (dag, lemmas) = build_dag(root_lemma, &precomputed)?;
        let root_slug = root_lemma.replace('/', "_");
        let dag_file = format!("../output/tmp_dag_{}.txt", root_slug);
        write_dag(&dag_file, &dag).map_err(|e| e.to_string())?;

        let lemmas_out_path = format!("../output/tmp_lemmas_{}.p", root_slug);
        let mut lemmas_txt = String::new();
        for (lemma_name, formula) in &lemmas {
            lemmas_txt.push_str(&format!(
                "fof({}, lemma,\n    {}\n).\n\n",
                lemma_name, formula
            ));
        }
        fs::write(&lemmas_out_path, &lemmas_txt)
            .map_err(|e| format!("Failed to write {}: {}", lemmas_out_path, e))?;

        // collect all history candidates which appear before the root
        let root_index_str = root_lemma.rsplit('_').next().unwrap(); // "0016"
                                                                     // (steps_total, history_lemma, annotated_proof)
        let mut local_best: Option<(usize, Option<String>, String)> = None;
        let mut candidates: Vec<String> = dag
            .keys()
            .filter(|k| is_small_step_lemma(k))
            .filter(|k| k.rsplit('_').next().unwrap() < root_index_str)
            .cloned()
            .collect();

        // collect all nodes: keys + all children
        let mut all_nodes: BTreeSet<String> = BTreeSet::new();
        for (parent, children) in &dag {
            all_nodes.insert(parent.clone());
            for child in children {
                all_nodes.insert(child.clone());
            }
        }
        let lemma_count = all_nodes.len();

        // fallback to single and abstract lemmas if empty

        // Two cases: the root can depend on single/abstract lemmas or the root itself is single/abstract
        if candidates.is_empty() {
            // extend the candidates with single and abstract lemmas
            // this can cause the root to be in the candidates too so we exclude it
            candidates.extend(
                dag.keys()
                    .filter(|k| {
                        (is_big_step_lemma(k) || is_abstracted_lemma(k)) && k != &root_lemma
                    })
                    .cloned(),
            );
            // if no single or abstract lemmas are present either, fallback to root-only proof
            // this is the second case: the root itself is single/abstract
            if candidates.is_empty() {
                let conjecture = extract_conjecture_from_file(input_file)?;
                if formulas_match(root_formula, &conjecture)
                    || formulas_match(&conjecture, root_formula)
                {
                    crate::klog_debug!("[DEBUG] Main theorem is root {} — skipping", root_lemma);
                    // don't re prove the main theorem
                    return Ok(());
                }

                let root_deps = dag.get(root_lemma).cloned().unwrap_or_default();
                let has_history_dependency = root_deps.iter().any(|d| is_small_step_lemma(d));

                // if this arises this is a bug in the DAG. so when the
                // duplicate is in itself. When we have cyclic dependencies.
                // this is a patch
                if candidates.is_empty() && has_history_dependency {
                    crate::klog_warn!(
                        "   [BUG] Root {} depends on history {:?} — refusing root-only proof",
                        root_lemma,
                        root_deps
                    );
                    return Ok(()); // skipping this now
                }
                crate::klog_debug!(
                    "   [INFO] No history or single lemmas found — falling back to root-only proof"
                );

                if is_small_step_lemma(root_lemma) {
                    // TODO this is a bug in the dag
                    crate::klog_warn!("   [BUG] No dependencies found — skipping");
                    return Ok(());
                }

                // vector to collect new Vampire lemmas (names + formulas)
                let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                let actual_file = select_actual_lemma(&proofs_dir, root_lemma)
                    .ok_or_else(|| format!("No proof file found for root {}", root_lemma))?;
                // try different variants
                let ext = [
                    format!("{}/{}.proof", proofs_dir, actual_file),
                    format!("{}/{}_twee.proof", proofs_dir, actual_file),
                    format!("{}/{}_vampire.proof", proofs_dir, actual_file),
                ];

                let path = ext.iter().find(|p| Path::new(p).exists()).ok_or_else(|| {
                    format!("No proof file found for root {} in any variant", root_lemma)
                })?;

                let mut root_proof = fs::read_to_string(path)
                    .map_err(|_| format!("Cannot read proof file {}", path))?;

                let prover = actual_file
                    .rsplit('_')
                    .next()
                    .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
                    .split('.')
                    .next()
                    .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
                    .to_string();

                // handle Vampire-specific prepending
                let (root_proof_steps, _root_proved_by) = if prover == "vampire" {
                    if let Some((superposition_steps, input_formulas, all_steps)) =
                        extract_superposition_steps(path, root_formula)
                    {
                        // prepend only the relevant Vampire steps and get the renaming
                        let (proof, renaming) = prepend_superposition_steps(
                            &extra_dependencies,
                            &superposition_steps,
                            &input_formulas,
                            &all_steps,
                        );
                        extend_with_superposition_steps(
                            &mut extra_dependencies,
                            &superposition_steps,
                            &renaming,
                        );
                        root_proof = proof;
                        (superposition_steps.len(), "vampire".to_string())
                    } else {
                        // fallback if extraction fails
                        (proof_length(&prover, &root_proof), "fallback".to_string())
                    }
                } else {
                    // Twee proof
                    (proof_length(&prover, &root_proof), "twee".to_string())
                };

                // we need to push what we already have proved to the extra dependencies for matching
                extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));

                let Some((sub_proof, sub_proof_steps, _sub_proved_by)) = prove_lemma(
                    input_file,
                    &lemmas_dir,
                    //None,
                    None,
                    &mut extra_dependencies,
                    None,
                )?
                else {
                    // no proof -> skip this candidate
                    return Ok(());
                };

                let annotated_proof = format!(
                    "% === Input Problem ===\n{}\n\n{}{}",
                    input_content, root_proof, sub_proof
                );

                let steps_total = root_proof_steps + sub_proof_steps;

                // root-only fallback:
                local_best = Some((steps_total, None, annotated_proof));
            } else {
                // basically here we are trying to prove the root from its single or abstract dependecies.
                // this is the first case: the root depends on single/abstract lemmas
                crate::klog_debug!(
                    "   [INFO] No history lemmas found — falling back to {} single lemmas",
                    candidates.len()
                );

                for candidate in &candidates {
                    crate::klog_debug!(
                        "   [INFO] Trying single/abstract candidate {} of {}",
                        candidate,
                        candidates.len()
                    );

                    let mut annotated_proof = String::new();
                    let mut steps_total = 0;

                    // check whether candidate is single or abstract
                    let is_single = is_big_step_lemma(candidate);
                    let is_abstract = is_abstracted_lemma(candidate);

                    // if we are falling back to single lemmas the superposition logic or indirect
                    // dependency proving logic will prove this directly. This means we will have
                    // to fall back in the 'no history used' logic below.
                    if is_single {
                        // 1. Get superposition steps
                        // get the lemma derived by superposition directly from Vampire proof
                        // in this case we are just proving the single lemma directly
                        let maybe_superposition =
                            superposition_steps(&dag_file, vampire_file, &lemmas_dir, candidate);
                        // in dependencies we will get itself (the single lemma)
                        // in this case we can ignore proved_history
                        let (dependencies, superposition_steps, _, input_formulas, all_steps) =
                            match maybe_superposition {
                                Some((deps, steps, ph, ipf, all)) => (deps, steps, ph, ipf, all),
                                None => (
                                    Vec::new(),
                                    BTreeMap::new(),
                                    false,
                                    BTreeMap::new(),
                                    BTreeMap::new(),
                                ),
                            };
                        let superposition_steps_count = superposition_steps.len();

                        // 2. Load dependency proofs
                        // load the proof of the single lemma
                        let dep_proofs = load_all_dependency_proofs(&proofs_dir, &dependencies)?;
                        // count the proof steps for the single lemma directly proven from the base axioms
                        let total_dep_steps: usize =
                            dep_proofs.iter().map(|(_, _, steps, _)| *steps).sum();
                        // combine all dependency proofs text (here this is probably useless since it's just one)
                        let combined_dep_proof_text = dep_proofs
                            .iter()
                            .map(|(_, _, _, text)| text.clone())
                            .collect::<Vec<_>>()
                            .join("\n\n"); // separate proofs by blank lines

                        // 3. Decide which source to use
                        let use_superposition = if total_dep_steps == 0 {
                            // no DAG dependencies -> must use superposition
                            true
                        } else {
                            // DAG dependencies exist -> use superposition only if it's shorter or equal
                            superposition_steps_count > 0
                                && superposition_steps_count <= total_dep_steps
                        };

                        // 4. Collect extra dependencies
                        let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                        // start lemmas
                        let (start_proof, start_proof_steps, start_proved_by) = if total_dep_steps
                            < superposition_steps_count
                            && total_dep_steps != 0
                        {
                            // we don't need to add anything to extra_dependencies
                            // TODO maybe merge dependencies and extra_dependencies?
                            (
                                combined_dep_proof_text.clone(),
                                total_dep_steps,
                                "fallback".to_string(),
                            )
                        } else {
                            // here the extra_dependencies are empty, we are at the start
                            // we also don't care about renaming because it's the initial superposition steps
                            let (sp_proof_text, renaming) = prepend_superposition_steps(
                                &extra_dependencies,
                                &superposition_steps,
                                &input_formulas,
                                &all_steps,
                            );
                            extend_with_superposition_steps(
                                &mut extra_dependencies,
                                &superposition_steps,
                                &renaming,
                            );
                            (
                                sp_proof_text,
                                superposition_steps_count,
                                "vampire".to_string(),
                            )
                        };

                        extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));

                        // 6. Compute root_proof
                        let Some((root_proof, root_proof_steps, root_proved_by)) = prove_lemma(
                            input_file,
                            &lemmas_dir,
                            // if use_superposition {
                            //     Some((superposition_steps, input_formulas))
                            // } else {
                            //     None
                            // }, // new superposition steps are in extra dependencies so we don't need them here
                            if use_superposition {
                                None
                            } else {
                                Some(&dependencies)
                            },
                            //vec![(root_lemma, &root_formula)],
                            &mut extra_dependencies, // if Vampire found the shortest proof then we have the new Vampire lemmas here
                            Some(root_lemma),
                        )?
                        else {
                            // no proof -> skip this candidate
                            continue;
                        };

                        // 7. Compute sub_proof / conjecture proof
                        let Some((sub_proof, sub_proof_steps, _sub_proved_by)) = prove_lemma(
                            input_file,
                            &lemmas_dir,
                            // if use_superposition {
                            //     Some((superposition_steps, input_formulas))
                            // } else {
                            //     None
                            // },
                            if use_superposition {
                                None
                            } else {
                                Some(&dependencies)
                            },
                            //vec![(root_lemma, &root_formula)],
                            &mut extra_dependencies, // the extra dependencies transfer here as axioms
                            None,
                        )?
                        else {
                            // no proof -> skip this candidate
                            continue;
                        };

                        let conjecture = extract_conjecture_from_file(input_file)?;
                        if formulas_match(root_formula, &conjecture)
                            || formulas_match(&conjecture, root_formula)
                        {
                            crate::klog_debug!(
                                "[DEBUG] Main theorem is root {} — skipping",
                                root_lemma
                            );
                            let (kept_start, _, kept_root, kept_start_steps, _, kept_root_steps) =
                                trim_proof_parts(
                                    Some((&start_proof, &start_proved_by, start_proof_steps)),
                                    None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                    (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                    None,
                                );

                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}",
                                input_content, kept_start, kept_root
                            );

                            // 8. Compute total steps
                            steps_total = kept_start_steps + kept_root_steps;
                        } else {
                            let (kept_start, _, kept_root, kept_start_steps, _, kept_root_steps) =
                                trim_proof_parts(
                                    Some((&start_proof, &start_proved_by, start_proof_steps)),
                                    None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                    (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                    Some(&sub_proof),
                                );

                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}{}",
                                input_content, kept_start, kept_root, sub_proof
                            );

                            // 8. Compute total steps
                            steps_total = kept_start_steps + kept_root_steps + sub_proof_steps;
                        }
                    }
                    // if we fall back to an abstract candidate we will have to prove
                    // it with Twee, we won't find it in the superposition steps.
                    else if is_abstract {
                        // 6. Compute (in this case find) root_proof
                        // construct the expected file path for the twee proof
                        let path = Path::new(&proofs_dir).join(format!("{}_twee.proof", candidate));

                        if path.exists() {
                            let abstract_proof = fs::read_to_string(&path).map_err(|_| {
                                format!("Cannot read proof file {}", path.display())
                            })?;

                            // extract prover
                            let prover = "twee".to_string();
                            let abstract_proof_steps = proof_length(&prover, &abstract_proof);

                            // load the formula of the abstracted lemma
                            let abstract_formula = match load_lemma(&lemmas_dir, candidate) {
                                Ok(f) => f,
                                Err(err) => {
                                    crate::klog_warn!(
                                        "     [WARN] Cannot load {}: {}. Skipping.",
                                        candidate,
                                        err
                                    );
                                    continue; // skip missing lemmas
                                }
                            };

                            // vector to collect new Vampire lemmas
                            let mut extra_dependencies: Vec<(String, String)> = Vec::new();
                            extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));
                            extra_dependencies
                                .push((candidate.to_string(), abstract_formula.clone()));

                            // 6. Compute root_proof
                            let Some((root_proof, root_proof_steps, root_proved_by)) = prove_lemma(
                                input_file,
                                &lemmas_dir,
                                None,
                                //vec![(root_lemma, &root_formula), (candidate, &abstract_formula)], // abstract lemma as dependency
                                &mut extra_dependencies,
                                Some(root_lemma),
                            )?
                            else {
                                // no proof -> skip this candidate
                                continue;
                            };

                            // 7. Compute sub_proof / conjecture proof
                            let Some((sub_proof, sub_proof_steps, _sub_proved_by)) = prove_lemma(
                                input_file,
                                &lemmas_dir,
                                None,
                                //vec![(root_lemma, &root_formula), (candidate, &abstract_formula)], // abstract lemma as dependency
                                &mut extra_dependencies, // here they might become None as we won't find the abstracted lemma in a Vampire proof(?)
                                None,
                            )?
                            else {
                                // no proof -> skip this candidate
                                continue;
                            };

                            let conjecture = extract_conjecture_from_file(input_file)?;
                            if formulas_match(root_formula, &conjecture)
                                || formulas_match(&conjecture, root_formula)
                            {
                                crate::klog_debug!(
                                    "   [INFO] Main theorem is root {} — skipping",
                                    root_lemma
                                );
                                // the goal was to prove something more abstract by dependencies, I doubt that in this case it will
                                // be helpful but let's TODO
                                continue;
                            }

                            let (
                                kept_abstract,
                                _,
                                kept_root,
                                kept_abstract_steps,
                                _,
                                kept_root_steps,
                            ) = trim_proof_parts(
                                Some((&abstract_proof, &prover, abstract_proof_steps)),
                                None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                Some(&sub_proof),
                            );

                            annotated_proof = format!(
                                "% === Input Problem ===\n{}\n\n{}{}{}",
                                input_content, kept_abstract, kept_root, sub_proof
                            );

                            // 8. Compute total steps
                            steps_total = kept_abstract_steps + kept_root_steps + sub_proof_steps;
                        } else {
                            crate::klog_warn!(
                                "   [WARN] Abstract lemma {} proof file does not exist, skipping",
                                candidate
                            );
                            continue; // skip this candidate if proof is missing
                        }
                    }
                    // single/history fallback:
                    // update local best
                    local_best = match local_best {
                        None => Some((steps_total, Some(candidate.clone()), annotated_proof)),
                        Some((best_steps, _, _)) => {
                            if steps_total < best_steps {
                                Some((steps_total, Some(candidate.clone()), annotated_proof))
                            } else {
                                local_best
                            }
                        }
                    };
                }
            }
        }
        // from now on we have history candidates
        else {
            // loop over all history candidates
            for n_history_lemma in &candidates {
                if n_history_lemma == root_lemma {
                    crate::klog_debug!(
                        "[INFO] Skipping history {} because it is the root lemma",
                        n_history_lemma
                    );
                    continue;
                }
                crate::klog_debug!(
                    "   [INFO] Trying history candidate {} of {}",
                    n_history_lemma,
                    candidates.len()
                );

                // 1. Get superposition steps
                // get the lemma derived by superposition directly from Vampire proof
                let maybe_superposition =
                    superposition_steps(&dag_file, vampire_file, &lemmas_dir, n_history_lemma);

                let (dependencies, superposition_steps, proved_history, input_formulas, all_steps) =
                    match maybe_superposition {
                        Some((deps, steps, ph, ipf, all)) => (deps, steps, ph, ipf, all),
                        None => (
                            Vec::new(),
                            BTreeMap::new(),
                            false,
                            BTreeMap::new(),
                            BTreeMap::new(),
                        ),
                    };
                let superposition_steps_count = superposition_steps.len();

                // If the history lemma is proved by superposition, the
                // dependencies vector will be empty. This means that we need to
                // compare the length of the history lemma proof with the
                // superposition steps The below code doesn't bother us cause
                // dependencies are empty and superposition will be chosen as
                // start proof.

                // check if it's already proven
                if dependencies.contains(n_history_lemma) {
                    crate::klog_debug!(
                        "[INFO] Skipping {} because it's already proven via superposition/dependencies",
                        n_history_lemma
                    );
                    continue;
                }

                if proved_history && !dependencies.is_empty() {
                    return Err("[ERROR] {} is already proven via superposition, dependencies should have been empty!!".into());
                }

                // 2. Load dependency proofs
                // load all dependency proofs and sum their steps
                let dep_proofs = load_all_dependency_proofs(&proofs_dir, &dependencies)?;
                // count the steps for all the dependencies
                let total_dep_steps: usize = dep_proofs.iter().map(|(_, _, steps, _)| *steps).sum();
                // combine all dependency proofs text
                let combined_dep_proof_text = dep_proofs
                    .iter()
                    .map(|(_, _, _, text)| text.clone())
                    .collect::<Vec<_>>()
                    .join("\n\n"); // separate proofs by blank lines

                // 3. Decide which source to use
                let use_superposition = if total_dep_steps == 0 {
                    // no DAG dependencies -> must use superposition
                    true
                } else {
                    // DAG dependencies exist -> use superposition only if it's shorter or equal
                    superposition_steps_count > 0 && superposition_steps_count <= total_dep_steps
                };

                // we need to compare the history proof we found with the existing start proof
                // in case this history lemma was already derived by superposition
                let prove_history = if use_superposition && proved_history {
                    // history lemma was already proved
                    false
                } else {
                    // either lemma was not proved or we are not using superposition
                    // and we are proving by dependencies
                    true
                };

                // 4. Build extra_dependencies before prepending
                let mut extra_dependencies: Vec<(String, String)> = Vec::new();

                // start lemmas
                let (start_proof, start_proof_steps, start_proved_by) =
                    if total_dep_steps < superposition_steps_count && total_dep_steps != 0 {
                        // we don't need to add the dependencies to the extra dependencies
                        // we already have them saved
                        (
                            combined_dep_proof_text.clone(),
                            total_dep_steps,
                            "fallback".to_string(),
                        )
                    } else {
                        // we build the start proof before adding the new superposition steps
                        // to the extra dependencies. This is because extra dependencies has
                        // to hold axioms for matching.
                        let (sp_proof_text, renaming) = prepend_superposition_steps(
                            &extra_dependencies,  // axioms for matching
                            &superposition_steps, // relevant vamp steps
                            &input_formulas,      // vamp input formulas
                            &all_steps,           // FULL proof graph
                        );
                        // here we add the new superposition steps
                        // to the extra dependencies to use them later
                        extend_with_superposition_steps(
                            &mut extra_dependencies,
                            &superposition_steps,
                            &renaming,
                        );
                        (
                            sp_proof_text,
                            superposition_steps_count,
                            "vampire".to_string(),
                        )
                    };

                // 4. Load n_history formula
                let n_formula = load_lemma(&lemmas_dir, n_history_lemma)
                    .map_err(|_| format!("Missing lemma {}", n_history_lemma))?;

                // add the axioms (in this case it will become the conjecture)
                extra_dependencies.push((n_history_lemma.to_string(), n_formula.clone()));

                // 6. Compute n_history_proof
                let Some((n_history_proof, n_history_proof_steps, n_history_proved_by)) =
                    prove_lemma(
                        input_file,
                        &lemmas_dir,
                        // if use_superposition {
                        //     Some((superposition_steps, input_formulas)) // TODO maybe this is dupl information and we don't need this
                        // } else {
                        //     None
                        // },
                        if use_superposition {
                            None
                        } else {
                            Some(&dependencies) // if we don't use superposition the dependencies are here
                        },
                        //vec![(&n_history_lemma, &n_formula)],
                        &mut extra_dependencies, // this now includes the new superposition steps after renaming
                        Some(n_history_lemma),
                    )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };

                extra_dependencies.push((root_lemma.to_string(), root_formula.clone()));

                // 7. Compute root_proof
                let Some((root_proof, root_proof_steps, root_proved_by)) = prove_lemma(
                    input_file,
                    &lemmas_dir,
                    // if use_superposition {
                    //     Some((superposition_steps, input_formulas))
                    // } else {
                    //     None
                    // },
                    if use_superposition {
                        None
                    } else {
                        Some(&dependencies)
                    },
                    //vec![(&n_history_lemma, &n_formula), (root_lemma, &root_formula)],
                    &mut extra_dependencies,
                    Some(root_lemma),
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };

                // 8. Compute sub_proof / conjecture proof
                let Some((sub_proof, sub_proof_steps, _sub_proved_by)) = prove_lemma(
                    input_file,
                    &lemmas_dir,
                    // if use_superposition {
                    //     Some((superposition_steps, input_formulas))
                    // } else {
                    //     None
                    // },
                    if use_superposition {
                        None
                    } else {
                        Some(&dependencies)
                    },
                    //vec![(&n_history_lemma, &n_formula), (root_lemma, &root_formula)],
                    &mut extra_dependencies,
                    None,
                )?
                else {
                    // no proof -> skip this candidate
                    continue;
                };

                // 9. Annotate all proofs
                let annotated_proof;
                let steps_total;
                if !prove_history {
                    crate::klog_debug!(
                        "   [INFO] History lemma {} already proved — skipping",
                        n_history_lemma
                    );

                    let conjecture = extract_conjecture_from_file(input_file)?;
                    if formulas_match(root_formula, &conjecture)
                        || formulas_match(&conjecture, root_formula)
                    {
                        // in this case here if root is the main theorem and we also have proved history
                        // we remain with start and root
                        crate::klog_debug!(
                            "[DEBUG] Main theorem is root {} — skipping",
                            root_lemma
                        );

                        let (kept_start, _, kept_root, kept_start_steps, _, kept_root_steps) =
                            trim_proof_parts(
                                Some((&start_proof, &start_proved_by, start_proof_steps)),
                                None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                None,
                            );

                        annotated_proof = format!(
                            "% === Input Problem ===\n{}\n\n{}{}",
                            input_content, kept_start, kept_root
                        );

                        // 10. Compute total steps
                        steps_total = kept_start_steps + kept_root_steps;
                    } else {
                        let (kept_start, _, kept_root, kept_start_steps, _, kept_root_steps) =
                            trim_proof_parts(
                                Some((&start_proof, &start_proved_by, start_proof_steps)),
                                None, // or Some((history_name, &history_proof, &history_by, history_steps))
                                (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                                Some(&sub_proof),
                            );

                        annotated_proof = format!(
                            "% === Input Problem ===\n{}\n\n{}{}{}",
                            input_content, kept_start, kept_root, sub_proof
                        );

                        // 10. Compute total steps
                        steps_total = kept_start_steps + kept_root_steps + sub_proof_steps;
                    }
                } else {
                    let conjecture = extract_conjecture_from_file(input_file)?;
                    if formulas_match(root_formula, &conjecture)
                        || formulas_match(&conjecture, root_formula)
                    {
                        crate::klog_debug!(
                            "[DEBUG] Main theorem is root {} — skipping",
                            root_lemma
                        );

                        let (
                            kept_start,
                            kept_history,
                            kept_root,
                            kept_start_steps,
                            kept_history_steps,
                            kept_root_steps,
                        ) = trim_proof_parts(
                            Some((&start_proof, &start_proved_by, start_proof_steps)),
                            Some((
                                n_history_lemma,
                                &n_history_proof,
                                &n_history_proved_by,
                                n_history_proof_steps,
                            )),
                            (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                            None,
                        );

                        // root and history were used
                        annotated_proof = format!(
                            "% === Input Problem ===\n{}\n\n{}{}{}",
                            input_content, kept_start, kept_history, kept_root
                        );

                        // 11. Compute total steps
                        steps_total = kept_start_steps + kept_history_steps + kept_root_steps;
                    } else {
                        let (
                            kept_start,
                            kept_history,
                            kept_root,
                            kept_start_steps,
                            kept_history_steps,
                            kept_root_steps,
                        ) = trim_proof_parts(
                            Some((&start_proof, &start_proved_by, start_proof_steps)),
                            Some((
                                n_history_lemma,
                                &n_history_proof,
                                &n_history_proved_by,
                                n_history_proof_steps,
                            )),
                            (root_lemma, &root_proof, &root_proved_by, root_proof_steps),
                            Some(&sub_proof),
                        );

                        // root and history were used
                        annotated_proof = format!(
                            "% === Input Problem ===\n{}\n\n{}{}{}{}",
                            input_content, kept_start, kept_history, kept_root, sub_proof
                        );

                        // 11. Compute total steps
                        steps_total = kept_start_steps
                            + kept_history_steps
                            + kept_root_steps
                            + sub_proof_steps;
                    }
                }

                // update local_best
                local_best = match local_best {
                    None => Some((steps_total, Some(n_history_lemma.clone()), annotated_proof)),
                    Some((best_steps, _, _)) => {
                        if steps_total < best_steps {
                            Some((steps_total, Some(n_history_lemma.clone()), annotated_proof))
                        } else {
                            local_best
                        }
                    }
                };

                crate::klog_debug!(
                    "   [INFO] Candidate root {} with history {} requires {} total steps with {} initial superposition steps",
                    root_lemma, n_history_lemma, steps_total, start_proof_steps
                );
            }
        }
        // update global_best
        if let Some((steps_total, best_history, annotated_proof)) = local_best {
            let candidate: RootEval = (
                lemma_count,
                steps_total,
                root_lemma.to_string(),
                best_history.unwrap_or_default(),
                annotated_proof,
                fs::read_to_string(&dag_file)
                    .map_err(|e| format!("Failed to read {}: {}", dag_file, e))?,
                fs::read_to_string(&lemmas_out_path)
                    .map_err(|e| format!("Failed to read {}: {}", lemmas_out_path, e))?,
            );

            let mut best_guard = global_best
                .lock()
                .map_err(|_| "Failed to lock global_best".to_string())?;

            match &*best_guard {
                None => {
                    *best_guard = Some(candidate);
                }
                Some((b_lemmas, b_steps, _, _, _, _, _)) => {
                    if candidate.1 < *b_steps
                        || (candidate.1 == *b_steps && candidate.0 < *b_lemmas)
                    {
                        *best_guard = Some(candidate);
                    }
                }
            }
        }

        let _ = fs::remove_file(&dag_file);
        let _ = fs::remove_file(&lemmas_out_path);
        Ok(())
    };

    if mode == ExecutionMode::Sequential {
        selected_roots.iter().try_for_each(&process_root)?;
    } else {
        selected_roots.par_iter().try_for_each(process_root)?;
    }

    let global_best = global_best
        .into_inner()
        .map_err(|_| "Failed to unwrap global_best".to_string())?;

    if let Some((_, steps, root, n_history, annotated_proof, dag_text, lemmas_text)) = &global_best
    {
        crate::klog_info!("[RESULT] Best combination found:");
        crate::klog_info!("[RESULT] Arrival lemma: {}", root);
        crate::klog_info!(
            "[RESULT] Departure lemma: {}",
            if n_history.is_empty() {
                "none"
            } else {
                n_history
            }
        );
        crate::klog_info!("[RESULT] Total steps: {}", steps);
        let vampire_steps = match fs::read_to_string(vampire_file) {
            Ok(content) => proof_length("vampire", &content),
            Err(_) => 0,
        };
        crate::klog_info!("[RESULT] Initial proof steps: {}", vampire_steps);
        crate::klog_info!("[RESULT] Minimized proof output: {}", proof_with_suffix);

        fs::write(dag_with_suffix.clone(), dag_text).map_err(|e| e.to_string())?;
        fs::write(lemmas_with_suffix.clone(), lemmas_text).map_err(|e| e.to_string())?;
        fs::write(proof_with_suffix.clone(), annotated_proof).map_err(|e| e.to_string())?;
    } else {
        return Err("No valid root/history candidate combination found.".into());
    }

    Ok("Minimization complete".into())
}

/// Proves a lemma using Twee and Vampire, selecting the shorter proof.
/// - `superposition_steps`: optional superposition steps to append
/// - `dependencies`: optional dependencies (lemma names)
/// - `axioms`: additional axioms to append
/// - `axioms`: existing dependencies, will be extended with new lemmas
/// - `conjecture`: optional lemma/conjecture to prove
pub fn prove_lemma(
    input_file: &str,
    lemmas_dir: &str,
    //    superposition_steps: Option<(BTreeMap<usize, SuperpositionStep>, BTreeMap<usize, String>)>,
    dependencies: Option<&[String]>,    // names
    axioms: &mut Vec<(String, String)>, // (name, formula)
    conjecture: Option<&str>,
) -> Result<Option<(String, usize, String)>, String> {
    let tmp_path = create_tmp_copy(input_file)?;
    let proofs_dir = "../proofs".to_string();

    // 1. Append dependency lemmas
    if let Some(deps) = dependencies {
        for dep_name in deps {
            let dep_formula = load_lemma(lemmas_dir, dep_name)
                .map_err(|_| format!("Missing lemma {}", dep_name))?;
            append_as_axiom(&tmp_path, &dep_formula, dep_name);
        }
    }

    // 2. Append extra dependencies
    if !axioms.is_empty() {
        for (name, formula) in axioms.iter() {
            append_as_axiom(&tmp_path, formula, name);
        }
    }

    // 3. Handle conjecture
    let (c_name, c_formula) = if let Some(s) = conjecture {
        let s = s.to_string();
        promote_axiom_to_conjecture(&tmp_path, &s)?;
        let formula = load_lemma(lemmas_dir, &s).map_err(|_| format!("Cannot load lemma {}", s))?;
        (s, formula)
    } else {
        let formula = extract_conjecture_from_file(input_file)?;
        ("conjecture".to_string(), formula)
    };

    // build a lookup-only axiom list that also includes the conjecture formula so that
    // Vampire input steps corresponding to the conjecture are named rather than falling
    // back to an a_N annotation (which looks like an unresolved reference in the output)
    let lookup_storage: Option<Vec<(String, String)>> = if axioms.iter().all(|(n, _)| n != &c_name)
    {
        let mut tmp = axioms.clone();
        tmp.push((c_name.clone(), c_formula.clone()));
        Some(tmp)
    } else {
        None
    };
    let axioms_for_lookup: &Vec<(String, String)> = lookup_storage.as_ref().unwrap_or(axioms);

    // 6. Run provers
    let twee_proof = run_twee(&tmp_path);
    let vampire_proof_file = format!("{}.vampire_proof", tmp_path);
    run_vampire(&tmp_path, &vampire_proof_file);
    let vampire_proof_exists = Path::new(&vampire_proof_file).exists();

    // 7. Select shorter proof (or better proof when --term-size-aware is on)
    let result: Option<(String, usize, String)> = match (twee_proof, vampire_proof_exists) {
        // Twee + Vampire available
        (Some(tp), true) => {
            let t_len = proof_length_twee(&tp);

            if let Some((sp_steps, input_formulas, all_steps)) =
                extract_superposition_steps(&vampire_proof_file, &c_formula)
            {
                let v_len = sp_steps.len();

                let chose_vampire = if term_size_aware() {
                    let vp_text = fs::read_to_string(&vampire_proof_file).unwrap_or_default();
                    let t_avg = avg_term_size_twee(&tp);
                    let v_avg = avg_term_size_vampire(&vp_text);
                    let better = proof_quality_better(v_len, v_avg, t_len, t_avg);
                    crate::klog_debug!(
                        "[DEBUG] prove_lemma: twee {} steps (avg_term={:.1}), vampire {} steps (avg_term={:.1}) → chose {}",
                        t_len, t_avg, v_len, v_avg,
                        if better { "vampire" } else { "twee" }
                    );
                    better
                } else if v_len < t_len {
                    crate::klog_debug!(
                        "[DEBUG] prove_lemma: twee {} steps, vampire {} steps → chose vampire",
                        t_len,
                        v_len
                    );
                    true
                } else {
                    crate::klog_debug!(
                        "[DEBUG] prove_lemma: twee {} steps, vampire {} steps → chose twee",
                        t_len,
                        v_len
                    );
                    false
                };

                if chose_vampire {
                    let (vp, renaming) = prepend_superposition_steps(
                        axioms_for_lookup,
                        &sp_steps,
                        &input_formulas,
                        &all_steps,
                    );
                    extend_with_superposition_steps(axioms, &sp_steps, &renaming);
                    let deduped_len = renaming.values().collect::<BTreeSet<_>>().len();
                    Some((vp, deduped_len, "vampire".to_string()))
                } else {
                    Some((tp, t_len, "twee".to_string()))
                }
            } else {
                crate::klog_debug!(
                    "[DEBUG] prove_lemma: twee {} steps, vampire: no superposition steps → chose twee",
                    t_len
                );
                Some((tp, t_len, "twee".to_string()))
            }
        }

        // Twee only
        (Some(tp), false) => {
            let t_len = proof_length_twee(&tp);
            crate::klog_debug!(
                "[DEBUG] prove_lemma: vampire: no proof, twee {} steps → chose twee",
                t_len
            );
            Some((tp, t_len, "twee".to_string()))
        }

        // Vampire only
        (None, true) => {
            let vp_text = fs::read_to_string(&vampire_proof_file)
                .map_err(|_| "Failed to read Vampire proof file")?;
            let v_len = proof_length_vampire(&vp_text);
            crate::klog_debug!(
                "[DEBUG] prove_lemma: twee: no proof, vampire {} steps → chose vampire",
                v_len
            );
            if let Some((sp_steps, input_formulas, all_steps)) =
                extract_superposition_steps(&vampire_proof_file, &c_formula)
            {
                let (vp, renaming) = prepend_superposition_steps(
                    axioms_for_lookup,
                    &sp_steps,
                    &input_formulas,
                    &all_steps,
                );
                extend_with_superposition_steps(axioms, &sp_steps, &renaming);
                let deduped_len = renaming.values().collect::<BTreeSet<_>>().len();
                Some((vp, deduped_len, "vampire".to_string()))
            } else {
                Some((vp_text, v_len, "vampire".to_string()))
            }
        }

        // no proof
        (None, false) => {
            crate::klog_debug!("[DEBUG] prove_lemma: no proof found by either prover");
            None
        }
    };

    // 8. Fallback: load an existing proof from proofs_dir (only if <= current best)
    let result: Option<(String, usize, String)> = match result {
        Some((best_proof, best_steps, best_by)) => {
            if let Ok((fb_proof, fb_steps)) = fallback_proof(&proofs_dir, &c_name, &c_formula) {
                if fb_steps < best_steps {
                    crate::klog_debug!(
                        "[DEBUG] prove_lemma: fallback {} steps < current {} steps → using fallback",
                        fb_steps, best_steps
                    );
                    Some((fb_proof, fb_steps, "fallback".to_string()))
                } else {
                    Some((best_proof, best_steps, best_by))
                }
            } else {
                Some((best_proof, best_steps, best_by))
            }
        }

        // no proof found in this run -> try fallback
        None => {
            if let Ok((fb_proof, fb_steps)) = fallback_proof(&proofs_dir, &c_name, &c_formula) {
                crate::klog_debug!(
                    "[DEBUG] prove_lemma: no proof from provers, fallback {} steps",
                    fb_steps
                );
                Some((fb_proof, fb_steps, "fallback".to_string()))
            } else {
                crate::klog_debug!("[DEBUG] prove_lemma: no proof found by any means");
                None
            }
        }
    };

    // 9. Cleanup temporary file
    let _ = fs::remove_file(&tmp_path);

    Ok(result)
}

fn is_single_or_abstract(name: &str) -> bool {
    is_big_step_lemma(name) || is_abstracted_lemma(name)
}

/// Fallback: load an existing proof from proofs_dir (any variant),
/// and if it's a Vampire proof try to prepend extracted superposition steps.
/// Returns (proof_text, step_count).
fn fallback_proof(
    proofs_dir: &str,
    lemma_name: &str,
    lemma_formula: &str,
) -> Result<(String, usize), String> {
    // restrict to single_lemma_* and abstract_lemma_* only
    // TODO but history_lemma_* is already what our tool does
    if !is_single_or_abstract(lemma_name) {
        return Err(format!(
            "[INFO] Fallback only applies to single and abstract lemmas, got {}",
            lemma_name
        ));
    }

    let actual_file = select_actual_lemma(proofs_dir, lemma_name)
        .ok_or_else(|| format!("No proof file found for {}", lemma_name))?;

    // try different variants
    let candidates = [
        format!("{}/{}.proof", proofs_dir, actual_file),
        format!("{}/{}_twee.proof", proofs_dir, actual_file),
        format!("{}/{}_vampire.proof", proofs_dir, actual_file),
    ];

    let path = candidates
        .iter()
        .find(|p| Path::new(p).exists())
        .ok_or_else(|| format!("No proof file found for {} in any variant", lemma_name))?;

    let mut proof_text =
        fs::read_to_string(path).map_err(|_| format!("Cannot read proof file {}", path))?;

    let prover = actual_file
        .rsplit('_')
        .next()
        .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
        .split('.')
        .next()
        .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
        .to_string();

    // handle Vampire-specific prepending
    let steps = if prover == "vampire" {
        //let extra_dependencies = Vec::new();
        if let Some((relevant_steps, input_formulas, all_steps)) =
            extract_superposition_steps(path, lemma_formula)
        {
            let (prepended, _renaming) = prepend_superposition_steps(
                &Vec::new(),     // no axioms in fallback mode
                &relevant_steps, // relevant steps (vamp -> VampStep)
                &input_formulas, // vamp -> input formula
                &all_steps,      // full proof graph (vamp -> VampStep)
            );
            // in case of a history problem we will have extra dependencies which we will need to prove
            //extend_with_superposition_steps(extra_dependencies, &superposition_steps, &renaming);

            let steps_init = proof_length(&prover, &proof_text);
            proof_text = prepended;
            //superposition_steps.len()
            steps_init
        } else {
            // extraction failed --> initial proof
            proof_length(&prover, &proof_text)
        }
    } else {
        proof_length(&prover, &proof_text)
    };

    Ok((proof_text, steps))
}

/// Returns true iff any proof segment uses the lemma.
/// Accepts any input variant like:
///   small_step_lemma_0060 / big_step_lemma_0060 / abstracted_lemma_0060 / lemma_0060
///   
/// By default we count:
///   - Axiom headers:  "Axiom k (lemma_0060):"
///   - deps mentions:  "deps: ... lemma_0060 ..." (with or without a trailing ':')
///
pub fn proof_uses_lemma(lemma_any_variant: &str, segments: &[&str]) -> bool {
    // extract trailing digits
    let num_re = Regex::new(r"(\d+)\s*$").unwrap();
    let Some(cap) = num_re.captures(lemma_any_variant.trim()) else {
        return false;
    };
    let num = cap.get(1).unwrap().as_str();

    // allow all variants
    let variants = [
        format!("small_step_lemma_{}", num),
        format!("big_step_lemma_{}", num),
        format!("abstracted_lemma_{}", num),
        format!("lemma_{}", num),
    ];

    // build alternation safely
    let alts = variants
        .iter()
        .map(|n| regex::escape(n))
        .collect::<Vec<_>>()
        .join("|");

    // 1) Present as an axiom: "Axiom 1 (single_lemma_0025): ..."
    let axiom_re = Regex::new(&format!(
        r"(?m)^\s*Axiom\s+\d+\s*\(\s*(?:{})\s*\)\s*:",
        alts
    ))
    .unwrap();

    // 2) Mentioned in deps (deps-only; does NOT match "% lemma_xxxx:" headers)
    // Handles:
    //   "| deps: lemma_0002, lemma_0003"
    //   "| deps: lemma_0003: <formula>, ..."
    let deps_re = Regex::new(&format!(
        r"(?mi)\|\s*deps\s*:\s*[^|\n]*\b(?:{})\b(?:\s*:)?",
        alts
    ))
    .unwrap();

    // 3) Proof-step citations (should be handled by the above)
    // Matches:
    //   "= { by axiom 2 (lemma_0003) }"
    //   "= { by lemma 5 (history_lemma_0061) R->L }"
    let cite_re = Regex::new(&format!(
        r"(?mi)\bby\s+(?:axiom|lemma)\s+\d+\s*\(\s*(?:{})\s*\)",
        alts
    ))
    .unwrap();

    segments
        .iter()
        .any(|s| axiom_re.is_match(s) || deps_re.is_match(s) || cite_re.is_match(s))
}

/// Keep only those lemmas in `block` that are required to derive
/// the lemmas referenced in later segments
pub fn trim_superposition_block(block: &str, later_segments: &[&str]) -> String {
    let header_re = Regex::new(r"(?m)^\s*%\s*===\s*Superposition Steps\s*===\s*$").unwrap();

    let lemma_line_re =
        Regex::new(r#"(?m)^\s*%\s*([A-Za-z_]*lemma_\d+)\s*:\s*(.*?)\s*(?:\|\s*deps:\s*(.*))?$"#)
            .unwrap();

    let dep_name_re = Regex::new(r"\b[A-Za-z_]*lemma_\d+\b").unwrap();

    // parse block order + deps
    let mut order: Vec<String> = Vec::new();
    let mut deps_map: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    for line in block.lines() {
        if let Some(cap) = lemma_line_re.captures(line) {
            let name = cap[1].to_string();
            order.push(name.clone());

            let deps_str = cap.get(3).map(|m| m.as_str()).unwrap_or("");
            let mut deps = BTreeSet::new();
            for m in dep_name_re.find_iter(deps_str) {
                deps.insert(m.as_str().to_string());
            }
            deps_map.insert(name, deps);
        }
    }

    if order.is_empty() {
        return block.to_string();
    }

    // roots: lemmas referenced later
    let in_block: BTreeSet<String> = order.iter().cloned().collect();
    let mut needed: BTreeSet<String> = BTreeSet::new();
    for name in &order {
        if proof_uses_lemma(name, later_segments) {
            needed.insert(name.clone());
        }
    }

    if needed.is_empty() {
        return String::new();
    }

    // optional: dependency closure *only to decide last needed point*
    let mut stack: Vec<String> = needed.iter().cloned().collect();
    while let Some(cur) = stack.pop() {
        if let Some(deps) = deps_map.get(&cur) {
            for d in deps {
                if in_block.contains(d) && !needed.contains(d) {
                    needed.insert(d.clone());
                    stack.push(d.clone());
                }
            }
        }
    }

    // IMPORTANT: prefix policy — keep everything up to the last needed lemma
    let mut last_idx: usize = 0;
    for (i, name) in order.iter().enumerate() {
        if needed.contains(name) {
            last_idx = last_idx.max(i);
        }
    }

    // rebuild: keep header + ALL lemma lines with index <= last_idx
    let mut out = String::new();
    let mut idx_map: BTreeMap<String, usize> = BTreeMap::new();
    for (i, n) in order.iter().enumerate() {
        idx_map.insert(n.clone(), i);
    }

    for line in block.lines() {
        if header_re.is_match(line) {
            out.push_str(line);
            out.push('\n');
            continue;
        }

        if let Some(cap) = lemma_line_re.captures(line) {
            let name = cap[1].to_string();
            if idx_map.get(&name).copied().unwrap_or(usize::MAX) <= last_idx {
                out.push_str(line);
                out.push('\n');
            }
        } else {
            // keep blank/comment lines
            if line.trim().is_empty() || line.trim_start().starts_with('%') {
                out.push_str(line);
                out.push('\n');
            }
        }
    }

    out
}

pub fn count_superposition_steps(block: &str) -> usize {
    let lemma_line_re = Regex::new(r"(?m)^\s*%\s*[A-Za-z_]*lemma_\d+\s*:").unwrap();
    lemma_line_re.find_iter(block).count()
}

// STOP-THE-BLEED: helpers
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum FreezeBefore {
    None,
    Start,   // don't trim start
    History, // don't trim start + history
    Root,    // don't trim start + history + root
}

/// Match a_2, a_6:, a_26, etc. (no fragile \b word-boundary)
fn has_bleed(text: &str) -> Option<u32> {
    // Require a colon after the number to avoid matching inside other tokens.
    // Also require a word boundary before `a_` so we don't match `lemma_a_0002` etc.
    let re = Regex::new(r"\ba_(\d+)\s*:").unwrap();
    for cap in re.captures_iter(text) {
        if let Ok(n) = cap[1].parse::<u32>() {
            if n != 1 {
                return Some(n);
            }
        }
    }
    None
}

/// Trims unecessary lemmas in proofs based on segments
/// TODO if start proof is not a superposition block but a Twee proof it doesn't trim it
pub fn trim_proof_parts(
    start: Option<(&str, &str, usize)>, // (start_text, start_proved_by, start_steps)
    history: Option<(&str, &str, &str, usize)>, // (history_name, history_text, history_proved_by, history_steps)
    root: (&str, &str, &str, usize), // (root_name, root_text, root_proved_by, root_steps)
    sub: Option<&str>,
) -> (
    String, // kept_start
    String, // kept_history
    String, // kept_root
    usize,  // start_steps
    usize,  // history_steps
    usize,  // root_steps
) {
    let (root_name, root_proof, root_by, root_steps_in) = root;

    // precompute sub segments (0 or 1 segment)
    let mut sub_segs: Vec<&str> = Vec::new();
    if let Some(s) = sub {
        if !s.trim().is_empty() {
            sub_segs.push(s);
        }
    }

    // If ANY vampire segment is raw (i.e., not our "% === Superposition Steps ===" block),
    // we disable trimming entirely and just return the segments as-is with provided step counts.
    let is_superposition_block = |txt: &str| -> bool {
        txt.lines()
            .any(|l| l.trim() == "% === Superposition Steps ===")
    };

    let any_raw_vampire = (start.is_some()
        && start.as_ref().unwrap().1 == "vampire"
        && !is_superposition_block(start.as_ref().unwrap().0))
        || (history.is_some()
            && history.as_ref().unwrap().2 == "vampire"
            && !is_superposition_block(history.as_ref().unwrap().1))
        || (root_by == "vampire" && !is_superposition_block(root_proof));

    if any_raw_vampire {
        let kept_start = start.map(|(t, _, _)| t.to_string()).unwrap_or_default();
        let kept_history = history
            .map(|(_, t, _, _)| t.to_string())
            .unwrap_or_default();
        let kept_root = root_proof.to_string();

        let start_steps = start.map(|(_, _, s)| s).unwrap_or(0);
        let history_steps = history.map(|(_, _, _, s)| s).unwrap_or(0);
        let root_steps = root_steps_in;

        return (
            kept_start,
            kept_history,
            kept_root,
            start_steps,
            history_steps,
            root_steps,
        );
    }

    // Run trimming once given a freeze level.
    let run = |freeze: FreezeBefore| -> (String, String, String, usize, usize, usize) {
        // helper: keep/trim a named segment
        let keep_named = |name: &str,
                          proof: &str,
                          by: &str,
                          steps_in: usize,
                          segs: &[&str]|
         -> (String, usize) {
            // TERMINAL RULE: if nothing comes after this segment, keep it.
            // (root becomes terminal when sub is absent)
            if segs.is_empty() {
                let kept = proof.to_string();
                let steps = if by == "vampire" {
                    count_superposition_steps(&kept)
                } else {
                    steps_in
                };
                return (kept, steps);
            }

            match by {
                "vampire" => {
                    let trimmed = trim_superposition_block(proof, segs);
                    let steps = count_superposition_steps(&trimmed);
                    (trimmed, steps)
                }
                "twee" => {
                    // if this segment isn't referenced later, drop it
                    if !proof_uses_lemma(name, segs) {
                        return (String::new(), 0);
                    }
                    (proof.to_string(), steps_in)
                }
                _ => (proof.to_string(), steps_in),
            }
        };

        // 1) root depends on sub (if any)
        let (kept_root, root_steps) = if freeze >= FreezeBefore::Root {
            (root_proof.to_string(), root_steps_in)
        } else {
            keep_named(root_name, root_proof, root_by, root_steps_in, &sub_segs)
        };

        // 2) history depends on root + sub
        let (kept_history, history_steps) = match history {
            None => (String::new(), 0),
            Some((h_name, h_proof, h_by, h_steps_in)) => {
                if freeze >= FreezeBefore::History {
                    let kept = h_proof.to_string();
                    if kept.trim().is_empty() {
                        (String::new(), 0)
                    } else {
                        (kept, h_steps_in)
                    }
                } else {
                    let mut segs: Vec<&str> = Vec::new();
                    if !kept_root.trim().is_empty() {
                        segs.push(&kept_root);
                    }
                    segs.extend(sub_segs.iter().copied());

                    let (kept, steps) = keep_named(h_name, h_proof, h_by, h_steps_in, &segs);
                    if kept.trim().is_empty() {
                        (String::new(), 0)
                    } else {
                        (kept, steps)
                    }
                }
            }
        };

        // 3) start depends on (history if non-empty) + root + sub
        let (kept_start, start_steps) = match start {
            None => (String::new(), 0),
            Some((start_proof, start_by, start_steps_in)) => {
                if freeze >= FreezeBefore::Start {
                    let kept = start_proof.to_string();
                    if kept.trim().is_empty() {
                        (String::new(), 0)
                    } else {
                        (kept, start_steps_in)
                    }
                } else {
                    let mut segs: Vec<&str> = Vec::new();
                    if !kept_history.trim().is_empty() {
                        segs.push(&kept_history);
                    }
                    if !kept_root.trim().is_empty() {
                        segs.push(&kept_root);
                    }
                    segs.extend(sub_segs.iter().copied());

                    let (kept, steps) = match start_by {
                        "vampire" => {
                            let trimmed = trim_superposition_block(start_proof, &segs);
                            let steps = count_superposition_steps(&trimmed);
                            (trimmed, steps)
                        }
                        _ => (start_proof.to_string(), start_steps_in),
                    };

                    if kept.trim().is_empty() {
                        (String::new(), 0)
                    } else {
                        (kept, steps)
                    }
                }
            }
        };

        (
            kept_start,
            kept_history,
            kept_root,
            start_steps,
            history_steps,
            root_steps,
        )
    };

    // PASS 1: normal trimming
    let first = run(FreezeBefore::None);
    let (ref kept_start_1, ref kept_history_1, ref kept_root_1, _, _, _) = first;

    // Decide freeze based on KEPT segments only (+ SUB, because it's always kept)
    let mut freeze2 = FreezeBefore::None;

    // if SUB has unresolved a_k:, freeze everything
    if freeze2 == FreezeBefore::None {
        if let Some(sub_txt) = sub {
            if !sub_txt.trim().is_empty() {
                if let Some(n) = has_bleed(sub_txt) {
                    freeze2 = FreezeBefore::Root;
                    crate::klog_debug!(
                        "[DEBUG] stop-the-bleed: unresolved a_{} in SUB; freezing trimming of start/history/root",
                        n
                    );
                }
            }
        }
    }

    if freeze2 == FreezeBefore::None {
        if let Some(n) = has_bleed(kept_root_1) {
            freeze2 = FreezeBefore::Root;
            crate::klog_debug!(
                "[DEBUG] stop-the-bleed: unresolved a_{} in KEPT ROOT; freezing trimming of start/history/root",
                n
            );
        }
    }

    if freeze2 == FreezeBefore::None && !kept_history_1.trim().is_empty() {
        if let Some(n) = has_bleed(kept_history_1) {
            freeze2 = FreezeBefore::History;
            crate::klog_debug!(
                "[DEBUG] stop-the-bleed: unresolved a_{} in KEPT HISTORY; freezing trimming of start/history",
                n
            );
        }
    }

    if freeze2 == FreezeBefore::None && !kept_start_1.trim().is_empty() {
        if let Some(n) = has_bleed(kept_start_1) {
            freeze2 = FreezeBefore::Start;
            crate::klog_debug!(
                "[DEBUG] stop-the-bleed: unresolved a_{} in KEPT START; freezing trimming of start",
                n
            );
        }
    }

    // PASS 2: re-run only if needed
    if freeze2 == FreezeBefore::None {
        first
    } else {
        run(freeze2)
    }
}
