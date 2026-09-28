use crate::alpha_match::normalize_formula_alpha;
use crate::prover_wrapper::proof_length;
use regex::Regex;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub struct PrecomputedLemmas {
    pub all_lemmas: BTreeMap<String, LemmaInfo>,
    pub all_twee: Vec<TweeDependency>,
    pub lemmas: BTreeMap<String, String>,
}

#[derive(Clone, Debug)]
pub struct LemmaInfo {
    pub formula: String,
    pub dependencies: Vec<(String, String)>,
}

#[derive(Clone, Debug)]
pub struct TweeDependency {
    pub name: String,
    pub formula: String,
    pub parents: Vec<String>,
}

// TODO optimization: precomputed lemmas takes the lemmas as they are in the proofs dir.
// we mix Vampire and Twee there. But here this is very Twee based so it would be good
// if we could take the shortest Twee proof as well and put it inside the precomputed lemmas.
// This would optimize. Ideally and a full fix would be to mix and match Vampire and Twee proofs
// depending on which is shorter for each lemma. But that is more complex to implement.
// In this way we would maybe find different proof paths that are shorter overall.
// (or just different, we cannot know if shorter yet)
// benchmark for this: ../benchmarks/input9/Equation3957_implies_Equation3971.p
// or prove these children by superposition as already tried
pub fn precompute_lemmas(
    proofs_dir: &str,
    lemmas_dir: &str,
    twee_proofs_dir: &str,
) -> Result<PrecomputedLemmas, String> {
    let mut all_lemmas: BTreeMap<String, LemmaInfo> = BTreeMap::new();
    let mut existing_lemmas: BTreeMap<String, String> = BTreeMap::new();
    let mut lemmas: BTreeMap<String, String> = BTreeMap::new();
    let mut all_twee: Vec<TweeDependency> = Vec::new();
    let mut next_index = 2;

    // precompute all lemmas
    for entry in fs::read_dir(proofs_dir).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        let path = entry.path();
        if path.is_dir() {
            continue;
        }

        // canonical lemma name (remove _twee/_vampire)
        let lemma_name = path
            .file_stem()
            .and_then(|s| s.to_str())
            .ok_or("Invalid proof file name")?
            .trim_end_matches("_twee")
            .trim_end_matches("_vampire")
            .to_string();

        // path to TWEE version
        let new_path = Path::new(twee_proofs_dir).join(format!("{}_twee.proof", lemma_name));
        let proof_content = match fs::read_to_string(&new_path) {
            Ok(c) => c,
            Err(_) => {
                // no twee proof for this lemma; register it with empty dependencies
                let formula = load_lemma(lemmas_dir, &lemma_name)?;
                all_lemmas.insert(
                    lemma_name,
                    LemmaInfo {
                        formula,
                        dependencies: Vec::new(),
                    },
                );
                continue;
            }
        };

        // extract dependencies
        let extracted = parse_used_lemmas(&proof_content, lemmas_dir, proofs_dir)?; // Vec<(name, formula)>
        let extracted_twee = extract_twee_lemmas(&proof_content); // Vec<(name, formula)>

        let mut dependencies: Vec<(String, String)> = Vec::new();
        for (dep_name, dep_formula) in extracted {
            dependencies.push((dep_name.clone(), dep_formula.clone()));
            lemmas.insert(dep_name, dep_formula);
        }

        // handle TWEE lemmas
        for (_twee_name, twee_formula) in extracted_twee {
            let key = normalize_formula_alpha(&twee_formula);
            let canonical_name = existing_lemmas
                .entry(key.clone())
                .or_insert_with(|| {
                    let name = format!("twee_lemma_{:02}", next_index);
                    next_index += 1;
                    name
                })
                .clone();

            // add parent if exists or create new
            if let Some(existing) = all_twee.iter_mut().find(|t| t.name == canonical_name) {
                if !existing.parents.contains(&lemma_name) {
                    existing.parents.push(lemma_name.clone());
                }
            } else {
                all_twee.push(TweeDependency {
                    name: canonical_name.clone(),
                    formula: twee_formula.clone(),
                    parents: vec![lemma_name.clone()],
                });
            }
            lemmas.insert(canonical_name.clone(), twee_formula.clone());
            dependencies.push((canonical_name, twee_formula));
        }

        let formula = load_lemma(lemmas_dir, &lemma_name)?;
        all_lemmas.insert(
            lemma_name.clone(),
            LemmaInfo {
                formula,
                dependencies,
            },
        );
    }

    Ok(PrecomputedLemmas {
        all_lemmas,
        all_twee,
        lemmas,
    })
}

/// Append a formula as an axiom to a file, adding quantifiers if needed
pub fn append_as_axiom(file_path: &str, formula: &str, lemma_name: &str) {
    let formula = formula.trim();

    // If the formula is already quantified, do NOT re-quantify
    let quantified_formula = if formula.starts_with("!") {
        formula.to_string()
    } else {
        // detect variables: uppercase X<number>
        let var_re = Regex::new(r"\b(X\d+)\b").unwrap();
        let mut vars: BTreeSet<String> = BTreeSet::new();

        for cap in var_re.captures_iter(formula) {
            vars.insert(cap[1].to_string());
        }

        if !vars.is_empty() {
            let vars_list = vars.into_iter().collect::<Vec<_>>().join(", ");
            let q = format!("! [{}] : ({})", vars_list, formula);
            q
        } else {
            formula.to_string()
        }
    };

    let axiom_text = format!("\nfof({}, axiom,\n{}\n).\n", lemma_name, quantified_formula);

    let current_content = fs::read_to_string(file_path).expect("Failed to read tmp input file");

    fs::write(file_path, format!("{}\n{}", current_content, axiom_text))
        .expect("Failed to append axiom");
}

/// Determine the actual lemma variant by checking the proofs folder.
/// Supports only canonical names (small_step/big_step/abstracted).
/// Returns the full filename including prover suffix.
pub fn select_actual_lemma(proofs_dir: &str, lemma_name: &str) -> Option<String> {
    // built-in axioms and conjectures just return the name
    if lemma_name.starts_with('a') || lemma_name.starts_with("conjecture_") {
        return Some(lemma_name.to_string());
    }

    let variants = ["small_step", "big_step", "abstracted"];
    let suffixes = ["_twee.proof", "_vampire.proof"];

    for var in &variants {
        // determine the base name to use in the filename
        let base_name = if lemma_name.starts_with(var) {
            lemma_name // already has the prefix
        } else {
            &format!("{}_{}", var, lemma_name) // prepend the variant
        };

        for suf in &suffixes {
            let filename_with_ext = format!("{}{}", base_name, suf);
            let proof_path = format!("{}/{}", proofs_dir, &filename_with_ext);

            if Path::new(&proof_path).exists() {
                // strip the ".proof" extension for the returned value
                return Some(
                    filename_with_ext
                        .strip_suffix(".proof")
                        .unwrap()
                        .to_string(),
                );
            }
        }
    }

    // no proof file exists
    None
}

/// Extract all Twee-generated lemmas from a proof output
pub fn extract_twee_lemmas(twee_output: &str) -> Vec<(String, String)> {
    let lemma_re = Regex::new(r"(?s)Lemma\s+(\d+):\s*(.*?)Proof:").unwrap();
    let mut result = Vec::new();

    // detect variables (all uppercase words)
    let var_re = Regex::new(r"\b([A-Z][0-9]*)\b").unwrap();
    for cap in lemma_re.captures_iter(twee_output) {
        let index: usize = cap[1].parse().unwrap();
        let body = cap[2].trim();

        // Take last line as the formula
        let mut formula_line = body
            .lines()
            .last()
            .map(|l| l.trim().to_string())
            .unwrap_or_else(|| body.to_string());

        if formula_line.ends_with('.') {
            formula_line.pop();
        }

        let mut vars: BTreeSet<String> = BTreeSet::new();
        for cap_var in var_re.captures_iter(&formula_line) {
            vars.insert(cap_var[1].to_string());
        }
        let var_list = vars.into_iter().collect::<Vec<_>>().join(", ");

        let lemma_name = format!("twee_lemma_{:02}", index);

        // Build only the body (wrap in universal quantifiers if variables exist)
        let formula_body = if var_list.is_empty() {
            formula_line
        } else {
            format!("! [{}] : ({})", var_list, formula_line)
        };

        result.push((lemma_name, formula_body));
    }

    result
}

/// Parse used lemmas from twee output and return their formulas
pub fn parse_used_lemmas(
    twee_output: &str,
    lemmas_dir: &str,
    proofs_dir: &str,
) -> Result<Vec<(String, String)>, String> {
    let axiom_re = Regex::new(r"Axiom\s+\d+\s+\(([^)]+)\)\s*:\s*(.+)").unwrap();
    let goal_re = Regex::new(r"Goal\s+\d+\s+\(([^)]+)\)\s*:\s*(.+)").unwrap();

    let mut used = Vec::new();

    for line in twee_output.lines() {
        // axioms
        if let Some(cap) = axiom_re.captures(line) {
            let name = cap[1].to_string();
            let formula = cap[2].trim().to_string();

            if name.starts_with('a') {
                used.push((name.clone(), formula.clone()));
                continue;
            }

            if name.starts_with("lemma_") {
                if let Some(actual) = select_actual_lemma(proofs_dir, &name) {
                    let clean = strip_prover_suffix(&actual);
                    let dep_formula = load_lemma(lemmas_dir, &clean)?;
                    used.push((clean, dep_formula));
                } else {
                    crate::klog_warn!("[WARN] No proof file found for {}", name);
                }
                continue;
            }

            if name.starts_with("conjecture_") {
                continue;
            }

            // any other symbol
            used.push((name.clone(), formula.clone()));
            continue;
        }

        // goals
        if let Some(cap) = goal_re.captures(line) {
            let name = cap[1].to_string();

            if name.starts_with("lemma_") {
                if let Some(actual) = select_actual_lemma(proofs_dir, &name) {
                    let clean = strip_prover_suffix(&actual);
                    let dep_formula = load_lemma(lemmas_dir, &clean)?;
                    used.push((clean, dep_formula));
                } else {
                    crate::klog_warn!("[WARN] No proof file found for {}", name);
                }
            }
        }
    }
    // deterministic order
    used.sort();
    Ok(used)
}

/// Load a specific lemma and extract its formula body.
/// Supports only canonical names (small_step/big_step/abstracted).
/// If lemma_name starts with "lemma_", treat it as "big_step_lemma_" for searching.
pub fn load_lemma(lemmas_dir: &str, lemma_name: &str) -> Result<String, String> {
    let lemma_name = strip_prover_suffix(lemma_name);

    // ordered lookup candidates
    let candidates: Vec<(String, String)> = if lemma_name.starts_with("big_step_lemma_") {
        vec![("big-step".to_string(), lemma_name.to_string())]
    } else if lemma_name.starts_with("small_step_lemma_") {
        vec![("small-step".to_string(), lemma_name.to_string())]
    } else if lemma_name.starts_with("abstracted_lemma_") {
        vec![("abstracted".to_string(), lemma_name.to_string())]
    } else if lemma_name.starts_with("lemma_") {
        vec![(
            "big-step".to_string(),
            lemma_name.replacen("lemma_", "big_step_lemma_", 1),
        )]
    } else {
        return Err(format!("[ERROR] Unknown lemma type for {}", lemma_name));
    };

    let mut resolved: Option<(std::path::PathBuf, String)> = None;
    for (subdir, file_lemma_name) in candidates {
        let file_path = Path::new(lemmas_dir)
            .join(subdir)
            .join(format!("{}.p", file_lemma_name));
        if file_path.exists() {
            resolved = Some((file_path, file_lemma_name));
            break;
        }
    }
    let (file_path, file_lemma_name) = resolved.ok_or_else(|| {
        format!(
            "[ERROR] File not found for lemma {} under {}",
            lemma_name, lemmas_dir
        )
    })?;

    let file_path_str = file_path
        .to_str()
        .ok_or_else(|| format!("[ERROR] Failed to convert path to string: {:?}", file_path))?;

    // determine internal TPTP name
    let internal_name = file_lemma_name
        .replace("big_step_lemma_", "conjecture_")
        .replace("small_step_lemma_", "conjecture_")
        .replace("abstracted_lemma_", "conjecture_");

    // extract formula body
    extract_tptp_formula_body(file_path_str, &internal_name)
        .map(|body| body.trim().to_string())
        .ok_or_else(|| {
            format!(
                "[ERROR] Formula for {} not found inside file {:?}",
                internal_name, file_path
            )
        })
}

/// Extract formula body for a given lemma from a TPTP file
pub fn extract_tptp_formula_body(file_path: &str, lemma: &str) -> Option<String> {
    let content = fs::read_to_string(file_path).ok()?;
    let mut lines_iter = content.lines();

    while let Some(line) = lines_iter.next() {
        if line.contains(lemma) {
            let mut formula_lines = Vec::new();
            if line.contains(").") {
                let start = line.find(',').unwrap_or(0);
                let mut body = &line[start..];
                // Remove the trailing ")."
                if let Some(pos) = body.rfind(").") {
                    body = &body[..pos];
                }
                formula_lines.push(body.trim().to_string());
            } else {
                for formula_line in lines_iter.by_ref() {
                    let trimmed = formula_line.trim();
                    if let Some(body) = trimmed.strip_suffix(").") {
                        formula_lines.push(body.to_string());
                        break;
                    } else {
                        formula_lines.push(trimmed.to_string());
                    }
                }
            }
            let formula_body = formula_lines.join(" ");
            return Some(formula_body);
        }
    }
    None
}

/// Extract the body of the first fof(..., conjecture, ...) in a TPTP file
pub fn extract_conjecture_from_file(path: &str) -> Result<String, String> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| format!("Failed to read file {}: {}", path, e))?;

    let mut in_conjecture = false;
    let mut formula_lines = Vec::new();

    for line in content.lines() {
        let trimmed = line.trim();
        if !in_conjecture {
            // Start of conjecture
            if trimmed.starts_with("fof") && trimmed.contains(", conjecture,") {
                in_conjecture = true;

                // collect everything after the first comma following "conjecture,"
                if let Some(idx) = trimmed.find(", conjecture,") {
                    let rest = &trimmed[idx + ", conjecture,".len()..].trim();
                    if !rest.is_empty() {
                        formula_lines.push(rest.to_string());
                    }
                }
            }
        } else {
            // inside conjecture, keep collecting lines
            formula_lines.push(trimmed.to_string());

            // stop if we find closing ")."
            if trimmed.ends_with(").") {
                break;
            }
        }
    }

    if formula_lines.is_empty() {
        return Err("No conjecture found in file".into());
    }

    // join all lines into one formula string, strip leading/trailing whitespace, remove ending ').'
    let mut formula = formula_lines.join(" ");
    formula = formula.trim().trim_end_matches(").").trim().to_string();

    Ok(formula)
}

/// Promote a root lemma to conjecture in a TPTP file.
///
/// - Removes any existing conjecture blocks.
/// - Finds the `fof` block with name == `root_lemma` and role == `axiom`,
///   and changes it to role `conjecture`.
/// - Leaves all other axioms unchanged.
pub fn promote_axiom_to_conjecture(path: &str, root_lemma: &str) -> Result<(), String> {
    let content = fs::read_to_string(path).map_err(|e| format!("read error: {}", e))?;

    // regex to match top-level fof/cnf blocks
    let r_fof = Regex::new(r"(?is)^\s*fof\s*\(\s*([^,]+)\s*,\s*([^,]+)\s*,(.*?)\)\s*\.\s*$")
        .map_err(|e| format!("regex error: {}", e))?;

    let mut out_blocks = Vec::new();

    for block in content.split_terminator(").\n") {
        let block_trimmed = block.trim();
        if block_trimmed.is_empty() {
            continue;
        }
        let block_full = format!("{}).\n", block_trimmed);

        if let Some(cap) = r_fof.captures(&block_full) {
            let name = cap.get(1).map(|m| m.as_str()).unwrap_or_default();
            let role = cap.get(2).map(|m| m.as_str()).unwrap_or_default();

            // remove existing conjectures entirely
            if role.to_lowercase().contains("conjecture") {
                continue;
            }

            // if this is the root lemma, promote to conjecture
            if name == root_lemma && role.to_lowercase() == "axiom" {
                let formula = cap.get(3).map(|m| m.as_str()).unwrap_or_default();
                let promoted = format!("fof({}, conjecture, {}).\n", name, formula);
                out_blocks.push(promoted);
                continue;
            }

            // otherwise, keep as-is
            out_blocks.push(block_full);
        } else {
            // non-fof block, keep as-is
            out_blocks.push(block_full);
        }
    }

    // Write back
    fs::write(path, out_blocks.join("\n")).map_err(|e| format!("write error: {}", e))?;

    Ok(())
}

pub fn create_tmp_copy(input_file: &str) -> Result<String, String> {
    let tmp_dir = Path::new("../lemmas/tmp");

    // ensure temp directory exists
    fs::create_dir_all(tmp_dir).map_err(|e| format!("Failed to create temp dir: {}", e))?;

    let input_path = Path::new(input_file);

    let file_stem = input_path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or("Invalid input filename")?;
    let ext = input_path
        .extension()
        .and_then(|s| s.to_str())
        .unwrap_or("p");

    // Include process id + high-resolution timestamp so concurrent minimization attempts
    // do not overwrite each other's temporary copies.
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| format!("Clock error: {}", e))?
        .as_nanos();
    let unique_name = format!("{}_{}_{}.{}", file_stem, std::process::id(), nanos, ext);
    let tmp_path: PathBuf = tmp_dir.join(unique_name);

    fs::copy(input_path, &tmp_path).map_err(|e| format!("Failed to copy temp input: {}", e))?;

    Ok(tmp_path.to_str().ok_or("Bad temp filename")?.to_string())
}

/// For a list of dependency lemma names, load all existing proofs
/// and compute steps using the correct prover.
/// Returns Vec of (lemma_name, prover, steps, proof_text) or Err if any proof cannot be loaded
pub fn load_all_dependency_proofs(
    proofs_dir: &str,
    dependencies: &[String],
) -> Result<Vec<(String, String, usize, String)>, String> {
    let mut result = Vec::new();

    for dep in dependencies {
        // try to find a matching file: e.g. "big_step_lemma_0047_twee.proof"
        let actual_file = select_actual_lemma(proofs_dir, dep)
            .ok_or_else(|| format!("No proof file found for dependency {}", dep))?;
        let path = format!("{}/{}.proof", proofs_dir, actual_file);

        // read file
        let text = std::fs::read_to_string(&path)
            .map_err(|_| format!("Cannot read proof file {}", actual_file))?;

        // extract prover inline from filename
        let prover = actual_file
            .rsplit('_') // split from last underscore
            .next() // get last segment, e.g. "twee.proof"
            .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
            .split('.') // split off extension
            .next() // get "twee"
            .ok_or_else(|| format!("Cannot extract prover from filename {}", actual_file))?
            .to_string();

        // count steps
        let steps = proof_length(&prover, &text);

        result.push((dep.clone(), prover, steps, text));
    }

    Ok(result)
}

/// Strips the prover suffix (_twee, _vampire) from a lemma name if present
pub fn strip_prover_suffix(lemma_name: &str) -> String {
    let suffixes = ["_twee", "_vampire"];
    for suf in &suffixes {
        if lemma_name.ends_with(suf) {
            return lemma_name.trim_end_matches(suf).to_string();
        }
    }
    lemma_name.to_string()
}

pub fn extract_suffix(path: &str) -> String {
    let stem = Path::new(path)
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .to_string();

    if let Some(stripped) = stem.strip_prefix("input_problem_") {
        stripped.to_string()
    } else {
        stem // fallback: whole stem
    }
}
