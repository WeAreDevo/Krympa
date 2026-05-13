use crate::prover_wrapper::{proof_length, prove_lemmas};
use crate::utils::*;
use regex::Regex;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

/// Phase 1: extract lemmas, and run provers on them.
/// Produces `summary.json` for use in Phase 2.
pub fn collect(input_file: &str, proof_file: &str, suffix: String) {
    crate::klog_info!("[INFO] Phase 1: Collection");
    crate::klog_debug!("[DEBUG] Input: {}", input_file);
    crate::klog_debug!("[DEBUG] Output: {}", proof_file);

    let lemmas_dir = "../lemmas".to_string();

    if Path::new(&lemmas_dir).exists() {
        for entry in fs::read_dir(&lemmas_dir).expect("Failed to read lemmas directory") {
            let entry = entry.expect("Failed to read directory entry");
            if entry.path().is_file() {
                fs::remove_file(entry.path()).expect("Failed to remove old lemma file");
            }
        }
        crate::klog_debug!("[DEBUG] Cleaned lemmas directory.");
    }

    let modes = ["big-step", "small-step", "abstracted"];
    let mut all_lemma_files = Vec::new();

    for mode in &modes {
        let mode_dir = format!("{}/{}", lemmas_dir, mode);
        if Path::new(&mode_dir).exists() {
            fs::remove_dir_all(&mode_dir).expect("Failed to clean mode directory");
        }
        fs::create_dir_all(&mode_dir).expect("Failed to create mode directory");

        // run OCaml parser to extract lemmas for the given mode
        run_ocaml_parser(proof_file, mode)
            .unwrap_or_else(|_| panic!("Failed to extract lemmas for mode '{}'", mode));

        // move extracted lemma files to mode directory
        for entry in fs::read_dir(&lemmas_dir).expect("Failed to read lemmas directory") {
            let path = entry.expect("Failed to read entry").path();
            if path.extension().map(|ext| ext == "p").unwrap_or(false) {
                let filename = path.file_name().unwrap();
                let new_path = Path::new(&mode_dir).join(filename);
                fs::rename(&path, &new_path).expect("Failed to move lemma file");
                all_lemma_files.push(new_path.to_string_lossy().to_string());
            }
        }
    }

    // run Stitch to generate abstracted_stitch_N/ variants
    let stitch_files = run_stitch_script(proof_file, &lemmas_dir);
    crate::klog_info!("[INFO] Stitch generated {} lemma file(s).", stitch_files.len());
    all_lemma_files.extend(stitch_files);

    // run provers on all lemma files
    let provers = ["vampire", "twee"];
    let results = prove_lemmas(&all_lemma_files, &provers, "../proofs");

    crate::klog_info!("[INFO] Phase 1 summary: {} lemmas proved.", results.len());
    let mut lemma_nums: Vec<u32> = results.keys().cloned().collect();
    lemma_nums.sort();
    crate::klog_debug!(
        "[DEBUG] Proved lemma ids: {}",
        lemma_nums
            .iter()
            .map(|n| format!("lemma_{:04}", n))
            .collect::<Vec<_>>()
            .join(", ")
    );

    // save summary for Phase 2
    let summary_file = format!("../output/summary_{}.json", suffix);
    let summary_json = serde_json::to_string_pretty(&results).expect("Failed to serialize results");
    fs::write(&summary_file, summary_json).expect("Failed to save summary.json");
    crate::klog_info!(
        "[INFO] Phase 1 complete. Summary saved to '{}'.",
        summary_file
    );
}

/// Phase 2: Shorten history proofs by replacing history lemmas with abstract lemmas
/// and rerunning provers on updated files.
pub fn shorten_proofs(summary_file: &str) {
    crate::klog_info!("[INFO] Phase 2: Shorten small-step proofs");

    let lemmas_dir = "../lemmas".to_string();
    let proofs_dir = "../proofs".to_string();
    let tmp_dirs = [
        ("vampire", "../proofs/vampire_tmp".to_string()),
        ("twee", "../proofs/twee_tmp".to_string()),
    ];

    let summary_data: HashMap<u32, (String, String, String)> = serde_json::from_str(
        &fs::read_to_string(summary_file).expect("Failed to read summary.json"),
    )
    .expect("Failed to parse summary.json");

    // map abstract lemma number -> formula
    let mut abstract_map: HashMap<u32, String> = HashMap::new();
    for (&n, (mode, _, _)) in &summary_data {
        if mode.starts_with("abstracted") {
            let lemma_name = mode.clone();
            let formula = match load_lemma(&lemmas_dir, &lemma_name) {
                Ok(f) => f,
                Err(err) => {
                    crate::klog_warn!("[WARN] Missing lemma {}: {}", lemma_name, err);
                    continue;
                }
            };
            crate::klog_debug!("[DEBUG] Abstract_{:04} formula extracted", n);
            abstract_map.insert(n, formula);
        }
    }

    let history_to_update: Vec<u32> = summary_data
        .iter()
        .filter(|(_, (mode, _, _))| mode.starts_with("small_step"))
        .map(|(n, _)| *n)
        .collect();

    crate::klog_info!(
        "[INFO] Small-step files to update: {}",
        history_to_update.len()
    );

    let block_re = Regex::new(r"(?s)(fof\(lemma_(\d{4}),\s*lemma\s*,.*?\)\s*\.)").unwrap();
    // replace history lemmas with abstract formulas
    for &history_file_num in &history_to_update {
        let history_file = format!(
            "{}/small-step/small_step_lemma_{:04}.p",
            lemmas_dir, history_file_num
        );
        let mut content = fs::read_to_string(&history_file)
            .unwrap_or_else(|_| panic!("Failed to read {}", history_file));

        let mut replaced_any = false;

        content = block_re
            .replace_all(&content, |caps: &regex::Captures| {
                let lemma_num: u32 = caps[2].parse().unwrap();
                if let Some(formula) = abstract_map.get(&lemma_num) {
                    crate::klog_debug!(
                        "[DEBUG] Replacing lemma_{:04} in history file {}",
                        lemma_num,
                        history_file_num
                    );
                    replaced_any = true;
                    format!("fof(lemma_{:04}, lemma,\n    {}\n).", lemma_num, formula)
                } else {
                    caps[1].to_string()
                }
            })
            .to_string();

        if replaced_any {
            fs::write(&history_file, content)
                .unwrap_or_else(|_| panic!("Failed to write {}", history_file));
        }
    }

    // rerun provers on updated history files
    let updated_files: Vec<String> = history_to_update
        .iter()
        .map(|n| format!("{}/small-step/small_step_lemma_{:04}.p", lemmas_dir, n))
        .collect();

    let provers = ["vampire", "twee"];
    fs::create_dir_all("../tmp").expect("Failed to create ../tmp directory");
    let updated_results = prove_lemmas(&updated_files, &provers, "../tmp"); // tmp root

    crate::klog_info!(
        "[INFO] Updated small-step proofs: {}",
        updated_results.len()
    );
    for (n, (mode, prover, proof)) in &updated_results {
        crate::klog_debug!(
            "[DEBUG] small_step_lemma_{:04} (mode: {}): '{}' with {} steps",
            n,
            mode,
            prover,
            proof_length(prover, proof)
        );

        // find prover-specific tmp dir
        let tmp_dir = tmp_dirs
            .iter()
            .find(|(p, _)| p == prover)
            .map(|(_, path)| path)
            .expect("Prover tmp dir not found");

        // tmp folder filename
        let proof_file_tmp =
            Path::new(tmp_dir).join(format!("small_step_lemma_{:04}_{}.proof", n, prover));
        fs::write(&proof_file_tmp, proof)
            .unwrap_or_else(|_| panic!("Failed to write proof file {}", proof_file_tmp.display()));

        // main proofs folder filename (same naming convention)
        let proof_file_main =
            Path::new(&proofs_dir).join(format!("small_step_lemma_{:04}_{}.proof", n, prover));
        fs::write(&proof_file_main, proof)
            .unwrap_or_else(|_| panic!("Failed to write proof file {}", proof_file_main.display()));
    }
}

/// Phase 3: Structural analysis of proofs. Groups lemmas by shared axioms
/// and saves results in a text file.
pub fn structural_groups(summary_file: &str) {
    use std::{collections::HashMap, fs, path::Path};

    crate::klog_info!("[INFO] Phase 3: Structural analysis");

    let proofs_dir = "../proofs".to_string();
    let output_groups_file = "../output/structural_groups.txt".to_string();

    // load summary.json
    let summary_data: HashMap<u32, (String, String, String)> = serde_json::from_str(
        &fs::read_to_string(summary_file).expect("Failed to read summary.json"),
    )
    .expect("Failed to parse summary.json");

    if summary_data.is_empty() {
        crate::klog_info!("[INFO] No proofs found in summary.json. Run Phase 1 first.");
        return;
    }

    let mut groups_output = String::new();
    groups_output.push_str("=== Structural Groups ===\n");

    // maps: key -> {lemma numbers}, key → {axioms}
    let mut groups: HashMap<String, Vec<u32>> = HashMap::new();
    let mut key_to_axioms: HashMap<String, Vec<String>> = HashMap::new();

    for (&lemma_num, (mode, prover, proof_text)) in &summary_data {
        // construct proof path: <proofs_dir>/<mode>_<prover>.proof
        let proof_path = format!("{}/{}_{}.proof", proofs_dir, mode, prover);

        let proof_content = if Path::new(&proof_path).exists() {
            fs::read_to_string(&proof_path).unwrap_or_else(|_| proof_text.clone())
        } else {
            proof_text.clone()
        };

        // extract axiom names from the proof
        let axioms = extract_axioms(&proof_content);

        if axioms.is_empty() {
            groups_output.push_str(&format!(
                "[WARN] lemma_{:04} has no recognizable axioms.\n",
                lemma_num
            ));
            continue;
        }

        // normalize: sorted axiom list becomes the key
        let mut key_vec: Vec<String> = axioms.iter().cloned().collect();
        key_vec.sort();
        let key = key_vec.join("|");

        key_to_axioms.insert(key.clone(), key_vec);
        groups.entry(key).or_default().push(lemma_num);
    }

    // print only real groups (with more than 1 lemma)
    for (key, lemmas) in &groups {
        if lemmas.len() > 1 {
            groups_output.push_str(&format!("\n[GROUP] Lemmas {:?}\n", lemmas));
            if let Some(axioms) = key_to_axioms.get(key) {
                groups_output.push_str("  Shared axioms:\n");
                for ax in axioms {
                    groups_output.push_str(&format!("    - {}\n", ax));
                }
            }
        }
    }

    // save the output to structural_groups.txt
    fs::write(&output_groups_file, groups_output)
        .expect("Failed to save structural groups to file");
    crate::klog_info!(
        "[INFO] Structural analysis complete. Groups saved to '{}'.",
        output_groups_file
    );
}

fn run_ocaml_parser(proof_file: &str, mode: &str) -> Result<(), String> {
    let parser_path = "ocaml_install/tptp_parser".to_string();
    let output = std::process::Command::new(parser_path)
        .arg(proof_file)
        .arg(mode)
        .output()
        .map_err(|e| format!("Failed to run OCaml parser executable: {}", e))?;

    if !output.status.success() {
        return Err(format!(
            "OCaml parser failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    crate::klog_debug!("{}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}

/// Run the Stitch Python script to generate abstracted_stitch_*/ lemma files.
/// Returns a list of all generated .p file paths.
fn run_stitch_script(_proof_file: &str, lemmas_dir: &str) -> Vec<String> {
    let script_path = "../python/run_stitch.py";
    let big_step_dir = format!("{}/big-step", lemmas_dir);

    // Prefer the repo's .venv python (which has stitch_core) over the system python3.
    let python = if std::path::Path::new("../.venv/bin/python").exists() {
        "../.venv/bin/python"
    } else {
        "python3"
    };

    let output = std::process::Command::new(python)
        .arg(script_path)
        .arg(&big_step_dir)
        .arg(lemmas_dir)
        .output();

    match output {
        Ok(out) => {
            crate::klog_debug!("[DEBUG] Stitch stderr: {}", String::from_utf8_lossy(&out.stderr));
            if !out.status.success() {
                crate::klog_warn!(
                    "[WARN] Stitch script exited with error: {}",
                    String::from_utf8_lossy(&out.stderr)
                );
            }
        }
        Err(e) => {
            crate::klog_warn!("[WARN] Failed to run Stitch script: {}", e);
            return Vec::new();
        }
    }

    // Scan for abstracted_stitch_* directories and collect .p files
    let mut stitch_files = Vec::new();
    let entries = match fs::read_dir(lemmas_dir) {
        Ok(e) => e,
        Err(_) => return Vec::new(),
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if !path.is_dir() {
            continue;
        }
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        if !name.starts_with("abstracted_stitch") {
            continue;
        }
        if let Ok(dir_entries) = fs::read_dir(&path) {
            for file_entry in dir_entries.flatten() {
                let file_path = file_entry.path();
                if file_path.extension().map(|e| e == "p").unwrap_or(false) {
                    stitch_files.push(file_path.to_string_lossy().to_string());
                }
            }
        }
    }

    stitch_files.sort();
    stitch_files
}

fn normalize_axiom(s: &str) -> String {
    s.replace([' ', '\n'], "")
        .replace("X0", "X")
        .replace("X1", "X")
        .replace("X2", "X")
        .replace("X3", "X")
        .replace("X4", "X")
        .replace("X5", "X")
        .replace("X6", "X")
        .replace("X7", "X")
        .replace("X8", "X")
        .replace("X9", "X")
        .replace("[input]", "")
        .trim()
        .to_string()
}

fn extract_axioms(proof_text: &str) -> HashSet<String> {
    let re_twee = Regex::new(r"(?m)^Axiom\s+\d+\s*\(.*?\):\s*(.*?)\.").unwrap();
    let re_vampire = Regex::new(r"(?m)^\d*\.?\s*! \[.*?\] : (.*?) \[input\]").unwrap();

    let mut set = HashSet::new();
    for cap in re_twee.captures_iter(proof_text) {
        set.insert(normalize_axiom(&cap[1]));
    }
    for cap in re_vampire.captures_iter(proof_text) {
        set.insert(normalize_axiom(&cap[1]));
    }
    set
}
