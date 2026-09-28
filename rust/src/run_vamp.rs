use crate::proof_turnaround::eq_proof_procedure;
use std::fs;
use std::path::Path;
use std::process::Command;

/// Run Vampire on a given input file and save its proof.
pub fn run_vampire_only(input: &str, output: &str) {
    let input_path = Path::new(input);
    if !input_path.exists() {
        crate::klog_error!(
            "[ERROR] Input file does not exist: {}",
            input_path.display()
        );
        return;
    }

    let output_path = Path::new(output);
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent).expect("Failed to create output directory");
    }

    crate::klog_info!("[INFO] Phase 0: Running Vampire and redirecting proof.");
    crate::klog_info!("[INFO] Input: {}", input_path.display());
    crate::klog_info!("[INFO] Output: {}", output_path.display());
    run_vampire(input_path.to_str().unwrap(), output_path.to_str().unwrap());
}

/// Helper: actually runs the Vampire binary
pub fn run_vampire(input_file: &str, output_file: &str) {
    let vampire_bin_name = if cfg!(target_os = "macos") {
        "../bin/vampire_mac"
    } else {
        "../bin/vampire"
    };
    let vampire_bin = Path::new(vampire_bin_name);

    let output = Command::new(vampire_bin)
        .arg(input_file)
        .output()
        .expect("Failed to run Vampire");

    // convert Vampire stdout to string
    let vampire_output =
        String::from_utf8(output.stdout).expect("Vampire output was not valid UTF-8");

    // turn the proof around + reformat
    let transformed_output = eq_proof_procedure(&vampire_output);

    // Write transformed proof
    fs::write(output_file, transformed_output).expect("Failed to write transformed Vampire output");

    crate::klog_debug!("[DEBUG] Vampire proof written to {}", output_file);
}
