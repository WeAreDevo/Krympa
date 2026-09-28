use crate::alpha_match::formulas_match;
use crate::dag::load_dag;
use crate::utils::*;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;

type AllSteps = BTreeMap<usize, VampStep>; // all steps (vamp -> step)
type InputFormulas = BTreeMap<usize, String>; // input_formulas (vamp -> formula)
type RelevantSteps = BTreeMap<usize, VampStep>; // only relevant (vamp -> step)

fn is_small_step_lemma(name: &str) -> bool {
    name.starts_with("small_step_lemma_")
}

fn is_big_step_lemma(name: &str) -> bool {
    name.starts_with("big_step_lemma_")
}

/// A single Vampire step (keyed by Vampire index).
#[derive(Debug, Clone)]
pub struct VampStep {
    pub formula: String,
    pub deps: Vec<usize>, // Vampire numbers
    pub is_input: bool,
}

/// Parse Vampire proof:
/// - returns all steps keyed by Vampire number
/// - returns input clauses (Vampire-number -> formula)
/// - returns relevant proof steps as a set of Vampire numbers (superposition/demodulation/...)
pub fn parse_vampire_proof(
    file_path: &str,
) -> Result<
    (
        AllSteps,        // all steps (vamp -> step)
        InputFormulas,   // input_formulas (vamp -> formula)
        BTreeSet<usize>, // relevant vamp indices
    ),
    String,
> {
    let content = fs::read_to_string(file_path).map_err(|e| e.to_string())?;

    let mut all_steps: AllSteps = BTreeMap::new();
    let mut input_formulas: InputFormulas = BTreeMap::new();
    let mut relevant: BTreeSet<usize> = BTreeSet::new();

    // keywords indicating relevant proof steps
    let proof_keywords = [
        "demodulation",
        "superposition",
        "resolution",
        "trivial inequality removal",
    ];

    for line in content.lines() {
        let line_trimmed = line.trim();
        if line_trimmed.is_empty() {
            continue;
        }

        // split using the last '[ ... ]' which is the inference tag
        let (main_part, tag_part) = match line_trimmed.rfind('[') {
            Some(i) => (
                line_trimmed[..i].trim(),
                line_trimmed[i + 1..].trim_end_matches(']').trim(),
            ),
            None => continue,
        };

        // extract Vampire number if present (from main_part)
        let vamp_num: usize = match main_part
            .split('.')
            .next()
            .and_then(|s| s.trim().parse::<usize>().ok())
        {
            Some(n) => n,
            None => continue,
        };

        // formula = main_part with leading "N." stripped
        let mut formula = main_part.to_string();
        if let Some(pos) = formula.find('.') {
            if formula[..pos].trim().parse::<usize>().is_ok() {
                formula = formula[pos + 1..].trim().to_string();
            }
        }

        // deps: numbers in tag_part
        let deps: Vec<usize> = tag_part
            .split([',', ' '])
            .filter_map(|s| s.trim().parse::<usize>().ok())
            .collect();

        let is_input = tag_part.contains("input");

        if is_input {
            input_formulas.insert(vamp_num, formula.clone());
        }

        if proof_keywords.iter().any(|k| tag_part.contains(k)) {
            relevant.insert(vamp_num);
        }

        all_steps.insert(
            vamp_num,
            VampStep {
                formula,
                deps,
                is_input,
            },
        );
    }

    Ok((all_steps, input_formulas, relevant))
}

/// Expand an arbitrary Vampire step number to the set of INPUT Vampire step numbers
/// by chasing deps through the FULL proof graph.
fn expand_to_inputs(
    start: usize,
    all_steps: &AllSteps,
    memo: &mut BTreeMap<usize, BTreeSet<usize>>,
    visiting: &mut BTreeSet<usize>,
) -> BTreeSet<usize> {
    if let Some(cached) = memo.get(&start) {
        return cached.clone();
    }
    if visiting.contains(&start) {
        return BTreeSet::new(); // cycle guard
    }
    visiting.insert(start);

    let mut out = BTreeSet::new();
    match all_steps.get(&start) {
        Some(step) if step.is_input => {
            out.insert(start);
        }
        Some(step) => {
            // not input: only recurse; if no deps => contributes no inputs
            for &d in &step.deps {
                out.extend(expand_to_inputs(d, all_steps, memo, visiting));
            }
        }
        None => {
            // unknown node => contributes no inputs
        }
    }

    visiting.remove(&start);
    memo.insert(start, out.clone());
    out
}

/// Collect all Vampire-step dependencies (transitively) within the FULL proof graph.
pub fn gather_all_vamp_dependencies(
    start: usize,
    all_steps: &AllSteps,
    collected: &mut BTreeSet<usize>,
) {
    if collected.contains(&start) {
        return;
    }
    collected.insert(start);

    if let Some(step) = all_steps.get(&start) {
        for &d in &step.deps {
            gather_all_vamp_dependencies(d, all_steps, collected);
        }
    }
}

/// Extract nth (history) lemma and matching Vampire steps.
///
/// Returns:
/// - dependency lemma names (from DAG)
/// - relevant Vampire steps (keyed by Vampire number)
/// - proved_history flag
/// - input_formulas (vamp->formula)
/// - full proof map (vamp->VampStep)
pub fn superposition_steps(
    dag: &str,
    vampire_file: &str,
    lemmas_dir: &str,
    lemma: &str,
) -> Option<(
    Vec<String>,
    RelevantSteps, // relevant steps as vampire-indexed map
    bool,
    InputFormulas, // input_formulas
    AllSteps,      // all_steps
)> {
    // load the DAG from a file. This DAG maps each lemma to its children.
    let dag = load_dag(dag);

    let (all_steps, input_formulas, relevant_set) = match parse_vampire_proof(vampire_file) {
        Ok(x) => x,
        Err(err) => {
            crate::klog_warn!(
                "  [WARN] Cannot parse vampire proof {}: {}",
                vampire_file,
                err
            );
            return None;
        }
    };

    let mut relevant_steps: RelevantSteps = BTreeMap::new();
    let mut proved_history = false;
    // TODO we might can do this a bit more elegantly but it works now:)
    let mut force_super = false;

    // build dependency lemma list from DAG
    let mut deps: Vec<String> = if is_small_step_lemma(lemma) {
        // for a history lemma, get its children in the DAG
        let children = match dag.get(lemma) {
            Some(c) => c,
            None => {
                crate::klog_warn!("   [WARN] No children for lemma {}", lemma);
                return None;
            }
        };

        // filter to only single children, if any exist
        let mut single_children: Vec<String> = children
            .iter()
            .filter(|c| is_big_step_lemma(c))
            .cloned()
            .collect();

        if single_children.is_empty() {
            crate::klog_debug!(
                "   [WARN] history lemma {} has no single lemma children; checking history children.",
                lemma
            );

            // gather history children of the lemma
            let history_children: Vec<String> = dag
                .get(lemma)
                .into_iter()
                .flat_map(|v| v.iter())
                .filter(|c| is_small_step_lemma(c))
                .cloned()
                .collect();

            // filter out children that are parents in the DAG
            let non_parent_history_children: Vec<String> = history_children
                .into_iter()
                .filter(|child| !dag.keys().any(|k| k != lemma && dag[k].contains(child)))
                .collect();

            if non_parent_history_children.is_empty() {
                // no non-parent history children -> prove history itself
                crate::klog_debug!(
                    "   [WARN] No non-parent history children found for {}; proving history directly.",
                    lemma
                );
                single_children.push(lemma.to_string());
                proved_history = true;
            } else {
                // use the non-parent history children as dependencies
                single_children = non_parent_history_children;
                force_super = true;
            }
        }

        single_children
    } else {
        // if not a history lemma, treat it as a single lemma
        // its own name is the dependency
        vec![lemma.to_string()]
    };

    // flag to check if any Vampire steps match the dependencies
    let mut matched_any = false;

    // match dependencies to Vampire relevant steps by formula
    for dep in &deps {
        // load the formula of the dependency lemma
        let dep_formula = match load_lemma(lemmas_dir, dep) {
            Ok(f) => f,
            Err(err) => {
                crate::klog_warn!("     [WARN] Cannot load {}: {}. Skipping.", dep, err);
                continue;
            }
        };

        // search only relevant vamp steps
        for &vnum in &relevant_set {
            let step = match all_steps.get(&vnum) {
                Some(s) => s,
                None => continue,
            };
            let wrapped = format!("({})", step.formula);

            // check if the dependency formula matches this step's formula
            if formulas_match(&dep_formula, &wrapped) {
                matched_any = true;

                // gather full transitive deps, then keep only relevant nodes among them
                let mut closure: BTreeSet<usize> = BTreeSet::new();
                gather_all_vamp_dependencies(vnum, &all_steps, &mut closure);

                for d in closure {
                    if relevant_set.contains(&d) {
                        if let Some(s) = all_steps.get(&d) {
                            relevant_steps.insert(d, s.clone());
                        }
                    }
                }

                break;
            }
        }
    }

    // return dependencies + matched Vampire steps if any were found
    if matched_any {
        if proved_history || force_super {
            // if we proved the history itself or forced superposition,
            // we have no other dependencies
            deps = Vec::new();
        }
        Some((
            deps,
            relevant_steps,
            proved_history,
            input_formulas,
            all_steps,
        ))
    } else {
        None
    }
}

/// Extract the exact derivation path (relevant-only) to prove a lemma formula.
/// Returns:
/// - relevant steps keyed by Vampire number
/// - input_formulas (vamp->formula)
/// - all_steps (vamp->VampStep)
pub fn extract_superposition_steps(
    vampire_file: &str,
    lemma_formula: &str,
) -> Option<(RelevantSteps, InputFormulas, AllSteps)> {
    let (all_steps, input_formulas, relevant_set) = match parse_vampire_proof(vampire_file) {
        Ok(x) => x,
        Err(err) => {
            crate::klog_warn!(
                "  [WARN] Cannot parse Vampire proof {}: {}",
                vampire_file,
                err
            );
            return None;
        }
    };

    // find a relevant vamp step proving the lemma
    let proving_vnum = relevant_set.iter().copied().find(|vnum| {
        all_steps
            .get(vnum)
            .map(|step| {
                formulas_match(lemma_formula, &step.formula)
                    || formulas_match(lemma_formula, &format!("({})", step.formula))
            })
            .unwrap_or(false)
    });

    if proving_vnum.is_none() {
        crate::klog_debug!(
            "[DEBUG] extract_superposition_steps: no step matched lemma formula: {}\n  relevant steps: {}",
            lemma_formula,
            relevant_set.iter()
                .filter_map(|v| all_steps.get(v).map(|s| format!("{}: {}", v, s.formula)))
                .collect::<Vec<_>>()
                .join("\n  ")
        );
    }

    let proving_vnum = proving_vnum?;

    // gather full transitive deps and keep only relevant ones
    let mut closure: BTreeSet<usize> = BTreeSet::new();
    gather_all_vamp_dependencies(proving_vnum, &all_steps, &mut closure);

    let mut relevant_steps: RelevantSteps = BTreeMap::new();
    for v in closure {
        if relevant_set.contains(&v) {
            if let Some(step) = all_steps.get(&v) {
                relevant_steps.insert(v, step.clone());
            }
        }
    }

    Some((relevant_steps, input_formulas, all_steps))
}

/// Extend extra_dependencies using the renaming map from prepending superposition steps
pub fn extend_with_superposition_steps(
    extra_dependencies: &mut Vec<(String, String)>,
    relevant_steps: &RelevantSteps,
    renaming: &BTreeMap<usize, String>,
) {
    for (vnum, step) in relevant_steps {
        let Some(name) = renaming.get(vnum) else {
            crate::klog_warn!("[WARN] Missing renaming for vamp {}", vnum);
            continue;
        };

        if extra_dependencies.iter().any(|(n, _)| n == name) {
            continue;
        }

        extra_dependencies.push((name.clone(), step.formula.clone()));
    }
}

/// Find the lemma indices already present in dependencies
fn used_lemma_numbers(axioms: &Vec<(String, String)>) -> BTreeSet<usize> {
    let re = Regex::new(r"(?:small_step_|big_step_|abstracted_)?lemma_(\d+)").unwrap();
    let mut used = BTreeSet::new();

    for (name, _) in axioms {
        for cap in re.captures_iter(name) {
            if let Ok(n) = cap[1].parse::<usize>() {
                used.insert(n);
            }
        }
    }

    used
}

/// Find the existing name of a lemma if available
fn find_existing_name_for_formula<'a>(
    axioms: &'a [(String, String)],
    step_formula: &str,
) -> Option<&'a str> {
    axioms
        .iter()
        .find(|(_, ax_f)| formulas_match(ax_f, step_formula) || formulas_match(step_formula, ax_f))
        .map(|(name, _)| name.as_str())
}

/// Prepend relevant Vampire steps and dependency formulas to a proof.
///
/// Key behavior change:
/// - deps that are not relevant steps are expanded (via FULL proof graph) to INPUT steps.
/// - those input steps are resolved to axiom names by formula matching when possible.
pub fn prepend_superposition_steps(
    axioms: &Vec<(String, String)>, // (name, formula)
    relevant_steps: &RelevantSteps, // (vamp -> step) only relevant
    input_formulas: &InputFormulas, // (vamp -> formula) for inputs
    all_steps: &AllSteps,           // full graph (vamp -> step)
) -> (String, BTreeMap<usize, String>) {
    // allocate lemma numbers from 1 upward, skipping already-used numbers
    let mut used = used_lemma_numbers(axioms);
    let mut next = 1usize;

    let mut fresh = || -> String {
        while used.contains(&next) {
            next += 1;
        }
        let n = next;
        used.insert(n);
        next += 1;
        format!("lemma_{:04}", n)
    };

    // build vamp -> global lemma name renaming for relevant steps.
    // also check steps already named in this run so equivalent formulas
    // (including reversed equality direction) collapse to the same name.
    let mut renaming: BTreeMap<usize, String> = BTreeMap::new();
    let mut seen_this_run: Vec<(String, String)> = Vec::new();
    for (vnum, step) in relevant_steps {
        if let Some(existing) = find_existing_name_for_formula(axioms, &step.formula) {
            renaming.insert(*vnum, existing.to_string());
        } else if let Some(existing) = find_existing_name_for_formula(&seen_this_run, &step.formula)
        {
            renaming.insert(*vnum, existing.to_string());
        } else {
            let name = fresh();
            seen_this_run.push((name.clone(), step.formula.clone()));
            renaming.insert(*vnum, name);
        }
    }

    let mut annotated = String::new();
    annotated.push_str("% === Superposition Steps ===\n");

    let mut memo: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut output_names: BTreeSet<String> = BTreeSet::new();

    for (vnum, step) in relevant_steps {
        let lemma_name = renaming.get(vnum).unwrap();

        // skip if an equivalent step was already output under this name
        if !output_names.insert(lemma_name.clone()) {
            continue;
        }

        let mut dep_strings: Vec<String> = Vec::new();
        let mut seen_dep_names: BTreeSet<String> = BTreeSet::new();

        for &d in &step.deps {
            if let Some(dep_lemma) = renaming.get(&d) {
                // skip if this dep name was already listed (dedup of equivalent steps)
                if !seen_dep_names.insert(dep_lemma.clone()) {
                    continue;
                }
                // dependency is another relevant step
                let dep_formula = relevant_steps
                    .get(&d)
                    .map(|s| s.formula.as_str())
                    .unwrap_or("UNKNOWN_FORMULA");
                dep_strings.push(format!("{}: {}", dep_lemma, dep_formula));
            } else {
                // dependency is non-relevant: expand to input leaves
                let mut visiting = BTreeSet::new();
                let inputs = expand_to_inputs(d, all_steps, &mut memo, &mut visiting);

                let mut resolved: Vec<String> = Vec::new();
                for iv in inputs {
                    // try resolve to axiom name
                    if let Some(inp_f) = input_formulas.get(&iv) {
                        if let Some((name, _)) =
                            axioms.iter().find(|(_, f)| formulas_match(f, inp_f))
                        {
                            resolved.push(name.clone());
                        } else {
                            resolved.push(format!("a_{}: {}", iv, inp_f));
                        }
                    } else if let Some(s) = all_steps.get(&iv) {
                        // fallback: show formula if we have it
                        resolved.push(format!("a_{}: {}", iv, s.formula));
                    } else {
                        resolved.push(format!("a_{}", iv));
                    }
                }

                resolved.sort();
                dep_strings.push(resolved.join(" + "));
            }
        }

        annotated.push_str(&format!(
            "% {}: {} | deps: {}\n",
            lemma_name,
            step.formula,
            dep_strings.join(", ")
        ));
    }

    annotated.push('\n');
    (annotated, renaming)
}
