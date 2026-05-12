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
    env::current_dir()
        .unwrap()
        .join("../bin/vampire")
        .to_str()
        .unwrap()
        .to_string()
}

fn twee_path() -> String {
    env::current_dir()
        .unwrap()
        .join("../bin/twee")
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

    // core inference indicators
    let proof_keywords = ["demodulation", "superposition", "resolution"];

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

    let mode = execution_mode();
    crate::klog_info!(
        "[INFO] Proving {} lemma groups in {} mode.",
        sorted_nums.len(),
        mode.as_str()
    );

    match mode {
        ExecutionMode::Parallel => sorted_nums
            .par_iter()
            .filter_map(|&n| {
                prove_lemma_group(n, &groups[&n], provers, &vampire_dir, &twee_dir, out_dir)
            })
            .collect(),
        ExecutionMode::Sequential => sorted_nums
            .iter()
            .filter_map(|&n| {
                prove_lemma_group(n, &groups[&n], provers, &vampire_dir, &twee_dir, out_dir)
            })
            .collect(),
    }
}

fn prove_lemma_group(
    n: u32,
    files: &[String],
    provers: &[&str],
    vampire_dir: &Path,
    twee_dir: &Path,
    out_dir: &Path,
) -> Option<(u32, (String, String, String))> {
    crate::klog_debug!("[DEBUG] Proving lemma {}", n);
    crate::klog_debug!(
        "[DEBUG] lemma {} running on thread {:?}",
        n,
        std::thread::current().id()
    );

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
                .to_lowercase();

            let len = if szs_status.contains("countersatisfiable")
                || szs_status.contains("counter-satisfiable")
                || szs_status.contains("counter_satisfiable")
                || (szs_status.contains("satisfiable") && !szs_status.contains("unsatisfiable"))
                || szs_status.contains("unknown")
            {
                1000
            } else {
                proof_length(&prover, &proof)
            };

            crate::klog_debug!("[DEBUG] {} proof length: {} lines", prover, len);
            all_proofs.push((prover, proof, len, file_stem.to_string()));
        }
    }

    if let Some((best_prover, best_proof, best_len, best_file)) =
        all_proofs.into_iter().min_by(|a, b| {
            if a.2 != b.2 {
                a.2.cmp(&b.2)
            } else {
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
