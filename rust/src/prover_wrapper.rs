use crate::execution::{execution_mode, ExecutionMode};
use rayon::prelude::*;
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::Path;
use std::time::Duration;
use wait_timeout::ChildExt;

fn run_external_prover(exe_path: &str, args: &[&str]) -> Option<String> {
    let mut child = match std::process::Command::new(exe_path)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            crate::klog_error!("[ERROR] Failed to start process '{}': {}", exe_path, e);
            return None;
        }
    };

    let timeout = Duration::from_secs(7);
    match child.wait_timeout(timeout).unwrap() {
        Some(status) => {
            let output = child.wait_with_output().unwrap();
            if status.success() {
                Some(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                crate::klog_debug!(
                    "[ERROR] Prover '{}' exited with error: {:?}",
                    exe_path,
                    status
                );
                let stderr = String::from_utf8_lossy(&output.stderr);
                crate::klog_debug!("[DEBUG] Stderr: {}", stderr);
                None
            }
        }
        None => {
            crate::klog_debug!(
                "[TIMEOUT] Prover '{}' exceeded {} seconds",
                exe_path,
                timeout.as_secs()
            );
            let _ = child.kill();
            None
        }
    }
}

fn vampire_path() -> String {
    let bin = if cfg!(target_os = "macos") {
        "vampire_mac"
    } else {
        "vampire"
    };
    env::current_dir()
        .unwrap()
        .join("../bin")
        .join(bin)
        .to_str()
        .unwrap()
        .to_string()
}

fn twee_path() -> String {
    let bin = if cfg!(target_os = "macos") {
        "twee_mac"
    } else {
        "twee"
    };
    env::current_dir()
        .unwrap()
        .join("../bin")
        .join(bin)
        .to_str()
        .unwrap()
        .to_string()
}

pub fn run_vampire(file: &str) -> Option<String> {
    run_external_prover(&vampire_path(), &["--input_syntax", "tptp", file])
}

pub fn run_twee(file: &str) -> Option<String> {
    run_external_prover(&twee_path(), &["--quiet", file])
}

/// Count Vampire proof steps, ignoring input/negated conjecture lines
/// Count Vampire proof steps based on core inference tags
pub fn proof_length_vampire(proof: &str) -> usize {
    let mut count = 0;

    // core inference indicators — must match superpose.rs parse_vampire_proof
    let proof_keywords = [
        "demodulation",
        "superposition",
        "resolution",
        "trivial inequality removal",
    ];

    for line in proof.lines() {
        let l = line.trim_start();

        // skip empty lines and comments
        if l.is_empty() || l.starts_with('%') {
            continue;
        }

        // remove leading line number (e.g., "23. ...")
        let l_no_num = if let Some(dot_pos) = l.find('.') {
            let (_, rest) = l.split_at(dot_pos + 1);
            rest.trim_start()
        } else {
            l
        };

        // only count lines whose inference tag contains one of the keywords
        if l_no_num.contains('[') && proof_keywords.iter().any(|kw| l_no_num.contains(kw)) {
            count += 1;
        }
    }

    count
}

pub fn proof_length_twee(proof: &str) -> usize {
    let mut in_proof = false;
    proof
        .lines()
        .map(str::trim_start)
        .filter(|line| {
            if line.starts_with("Proof:") {
                in_proof = true;
                return false;
            }
            in_proof && line.contains("= { by")
        })
        .count()
}

pub fn proof_length(prover: &str, proof: &str) -> usize {
    match prover {
        "vampire" => proof_length_vampire(proof),
        "twee" => proof_length_twee(proof),
        _ => proof.lines().count(),
    }
}

/// Number of `op(` nodes in a term — a measure of structural complexity.
/// A bare variable scores 1 (minimum meaningful unit).
fn term_size(term: &str) -> usize {
    term.matches("op(").count() * 2 + 1
}

/// Average term size across all intermediate terms in a twee proof.
/// Counts every line inside a `Proof:` block that is not a `= { by … }` step line.
pub fn avg_term_size_twee(proof: &str) -> f64 {
    let mut in_proof = false;
    let mut sizes: Vec<usize> = Vec::new();

    for line in proof.lines() {
        let t = line.trim();
        if t.starts_with("Proof:") {
            in_proof = true;
            continue;
        }
        // New section starts, exits the proof block
        if t.starts_with("Lemma ") || t.starts_with("Goal ") || t.starts_with("RESULT") {
            in_proof = false;
            continue;
        }
        if !in_proof || t.is_empty() {
            continue;
        }
        // Skip step lines: "= { by … }"
        if t.starts_with("= {") {
            continue;
        }
        sizes.push(term_size(t));
    }

    if sizes.is_empty() {
        return 0.0;
    }
    sizes.iter().sum::<usize>() as f64 / sizes.len() as f64
}

/// Average term size across all inference-step formulas in a vampire proof.
/// Only considers superposition / demodulation / resolution steps.
/// For each such step the formula is split on `=` / `!=` and both sides are measured.
pub fn avg_term_size_vampire(proof: &str) -> f64 {
    let proof_keywords = [
        "demodulation",
        "superposition",
        "resolution",
        "trivial inequality removal",
    ];
    let mut sizes: Vec<usize> = Vec::new();

    for line in proof.lines() {
        let l = line.trim_start();
        if l.is_empty() || l.starts_with('%') {
            continue;
        }
        // Strip leading line number "N. "
        let l_no_num = if let Some(dot_pos) = l.find('.') {
            l[dot_pos + 1..].trim_start()
        } else {
            l
        };
        if !l_no_num.contains('[') || !proof_keywords.iter().any(|kw| l_no_num.contains(kw)) {
            continue;
        }
        // Formula is everything before the last `[`
        let formula = match l_no_num.rfind('[') {
            Some(pos) => l_no_num[..pos].trim(),
            None => continue,
        };
        // Strip universal quantifier "! [X0,…] : body" if present
        let body = if formula.starts_with("! [") {
            match formula.find("] : ") {
                Some(pos) => formula[pos + 4..].trim(),
                None => formula,
            }
        } else {
            formula
        };
        // Split equation into its two sides; fall back to treating the whole body as one term
        if let Some(pos) = body.find(" != ") {
            sizes.push(term_size(body[..pos].trim()));
            sizes.push(term_size(body[pos + 4..].trim()));
        } else if let Some(pos) = body.find(" = ") {
            sizes.push(term_size(body[..pos].trim()));
            sizes.push(term_size(body[pos + 3..].trim()));
        } else {
            sizes.push(term_size(body));
        }
    }

    if sizes.is_empty() {
        return 0.0;
    }
    sizes.iter().sum::<usize>() as f64 / sizes.len() as f64
}

/// When `--term-size` is on, proof A is better than proof B if:
///   • A has strictly fewer steps, OR
///   • A has lower average term size and is at most TOLERANCE × longer.
/// Falls back to pure step-count comparison when term sizes are equal.
const TERM_SIZE_TOLERANCE: f64 = 1.5;

pub fn proof_quality_better(a_steps: usize, a_avg: f64, b_steps: usize, b_avg: f64) -> bool {
    if a_steps == b_steps {
        a_avg < b_avg
    } else if a_steps < b_steps {
        // A is shorter — A wins unless B has lower avg and is within tolerance
        !(b_avg < a_avg && b_steps as f64 <= a_steps as f64 * TERM_SIZE_TOLERANCE)
    } else {
        // B is shorter — A wins only if A has lower avg and is within tolerance
        a_avg < b_avg && a_steps as f64 <= b_steps as f64 * TERM_SIZE_TOLERANCE
    }
}

pub fn prove_lemmas(
    lemma_files: &[String],
    provers: &[&str],
    out_dir_path: &str,
) -> HashMap<u32, (String, String, String)> {
    let out_dir = Path::new(out_dir_path);
    if out_dir.exists() {
        fs::remove_dir_all(out_dir).unwrap();
    }
    fs::create_dir_all(out_dir).unwrap();

    let vampire_dir = out_dir.join("vampire_tmp");
    let twee_dir = out_dir.join("twee_tmp");
    fs::create_dir_all(&vampire_dir).unwrap();
    fs::create_dir_all(&twee_dir).unwrap();

    // group by lemma index
    let mut groups: HashMap<u32, Vec<String>> = HashMap::new();
    for f in lemma_files {
        let fname = Path::new(f).file_stem().unwrap().to_string_lossy();
        let num: u32 = fname
            .chars()
            .rev()
            .take_while(|c| c.is_ascii_digit())
            .collect::<String>()
            .chars()
            .rev()
            .collect::<String>()
            .parse()
            .unwrap_or(0);
        groups.entry(num).or_default().push(f.clone());
    }

    let mut sorted_nums: Vec<u32> = groups.keys().cloned().collect();
    sorted_nums.sort();

    let process_n = |&n: &u32| -> Option<(u32, (String, String, String))> {
        crate::klog_debug!("[DEBUG] Proving lemma {}", n);
        crate::klog_debug!(
            "[DEBUG] lemma {} running on thread {:?}",
            n,
            std::thread::current().id()
        );

        let files = &groups[&n];

        // collect all successful proofs for this group
        let mut all_proofs: Vec<(String, String, usize, String)> = Vec::new(); // (prover, proof, len, filename)

        for lemma_file in files {
            let file_stem = Path::new(lemma_file).file_stem().unwrap().to_string_lossy();
            let vampire_file = vampire_dir.join(format!("{}_vampire.proof", file_stem));
            let twee_file = twee_dir.join(format!("{}_twee.proof", file_stem));

            for (prover, proof) in try_provers(lemma_file, provers, &vampire_file, &twee_file) {
                let szs_status = proof
                    .lines()
                    .find(|l| l.contains("RESULT:") || l.contains("SZS status"))
                    .unwrap_or("")
                    .to_lowercase(); // normalize to lowercase

                let len = if szs_status.contains("countersatisfiable")
                    || szs_status.contains("counter-satisfiable")
                    || szs_status.contains("counter_satisfiable")
                    || (szs_status.contains("satisfiable") && !szs_status.contains("unsatisfiable"))
                    || szs_status.contains("unknown")
                {
                    1000 // sentinel for non-theorem / countersat / unknown
                         // TODO we can use them. But for now we just want shortest
                         // theorem proofs. Later we can see how we prove the
                         // conjecture from the satisfiable ones.
                } else {
                    proof_length(&prover, &proof)
                };

                //let len = proof_length(&prover, &proof);
                crate::klog_debug!("[DEBUG] {} proof length: {} lines", prover, len);
                all_proofs.push((prover, proof, len, file_stem.to_string()));
            }
        }

        // pick the shortest proof across all modes and provers
        if let Some((best_prover, best_proof, best_len, best_file)) =
            all_proofs.into_iter().min_by(|a, b| {
                // compare lengths first
                if a.2 != b.2 {
                    a.2.cmp(&b.2)
                } else {
                    // Tie-breaker: prefer "twee" over "vampire" over others
                    let order = |p: &String| {
                        if p == "twee" {
                            0
                        } else if p == "vampire" {
                            1
                        } else {
                            2
                        }
                    };
                    order(&a.0).cmp(&order(&b.0))
                }
            })
        {
            let final_path = out_dir.join(format!("{}_{}.proof", best_file, best_prover));
            if let Err(e) = fs::write(&final_path, &best_proof) {
                crate::klog_error!("[ERROR] Failed to save shortest proof: {}", e);
            } else {
                crate::klog_debug!("[DEBUG] Saved shortest proof to '{}'", final_path.display());
            }

            crate::klog_debug!(
                "[DEBUG] Shortest proof for lemma {} found in '{}' by '{}' with {} lines",
                n,
                best_file,
                best_prover,
                best_len
            );

            Some((n, (best_file, best_prover, best_proof)))
        } else {
            crate::klog_warn!("[WARN] No successful proof for group {}", n);
            None
        }
    };

    if execution_mode() == ExecutionMode::Sequential {
        sorted_nums.iter().filter_map(&process_n).collect()
    } else {
        sorted_nums.par_iter().filter_map(&process_n).collect()
    }
}

fn try_provers(
    lemma_file: &str,
    provers: &[&str],
    vampire_file: &Path,
    twee_file: &Path,
) -> Vec<(String, String)> {
    let mut successes = Vec::new();

    for &prover in provers {
        let output_file = match prover {
            "vampire" => vampire_file,
            "twee" => twee_file,
            _ => {
                crate::klog_error!("[ERROR] Unknown prover '{}'", prover);
                continue;
            }
        };

        crate::klog_debug!("[RUN] Trying prover '{}' on '{}'", prover, lemma_file);

        let proof_content = match prover {
            "vampire" => match run_vampire(lemma_file) {
                Some(c) => c,
                None => {
                    crate::klog_debug!("[DEBUG] Vampire failed for '{}'", lemma_file);
                    continue;
                }
            },
            "twee" => match run_twee(lemma_file) {
                Some(c) => c,
                None => {
                    crate::klog_debug!("[DEBUG] Twee failed for '{}'", lemma_file);
                    continue;
                }
            },
            _ => continue,
        };

        if let Err(e) = fs::write(output_file, &proof_content) {
            crate::klog_error!(
                "[ERROR] Failed to save proof for prover '{}': {}",
                prover,
                e
            );
        }

        successes.push((prover.to_string(), proof_content));
    }

    successes
}
