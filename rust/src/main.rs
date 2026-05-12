use krympa::execution::{parse_execution_mode_args, set_execution_mode};
use krympa::utils::extract_suffix;
use krympa::{core, minimize, run_vamp};
use std::env;

fn main() {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    let (mode, args) = match parse_execution_mode_args(&raw_args) {
        Ok(parsed) => parsed,
        Err(err) => {
            krympa::klog_error!("{}", err);
            return;
        }
    };

    if let Err(err) = set_execution_mode(mode) {
        krympa::klog_error!("{}", err);
        return;
    }

    if args.is_empty() {
        krympa::klog_error!(
            "Usage: cargo run -- [--parallel|--sequential] [collect|shorten|group|minimize|run_vampire] <input_file>"
        );
        krympa::klog_error!(
            "Usage for benchmarking: cargo run --bin benchmarking -- [--parallel|--sequential] <input_folder> <timeout_secs> [krympa_binary]"
        );
        return;
    }
    krympa::klog_info!("[INFO] Execution mode: {}", mode.as_str());

    match args[0].as_str() {
        "collect" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: cargo run -- collect <input_file>");
            } else {
                let input_file = &args[1];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);
                core::collect(input_file, &output_file, suffix);
            }
        }
        "shorten" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: cargo run -- collect <input_file>");
            } else {
                let input_file = &args[1];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let summary_file = format!("../output/summary_{}.json", suffix);
                core::shorten_proofs(&summary_file)
            }
        }
        "group" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: cargo run -- collect <input_file>");
            } else {
                let input_file = &args[1];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let summary_file = format!("../output/summary_{}.json", suffix);
                core::structural_groups(&summary_file)
            }
        }
        "minimize" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: cargo run -- minimize <input_file>");
            } else {
                let input_file = &args[1];

                // extract suffix from input file
                let suffix = extract_suffix(input_file);

                // construct summary and output files with suffix
                let summary_file = format!("../output/summary_{}.json", suffix);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);

                // call minimize with input file and suffixed summary
                match minimize::try_minimize(input_file, &output_file, &summary_file) {
                    Ok(msg) => krympa::klog_info!("{}", msg),
                    Err(err) => krympa::klog_error!("Error: {}", err),
                }
            }
        }
        "run_vampire" => {
            if args.len() < 2 {
                krympa::klog_error!("Usage: cargo run -- run_vampire <input_file>");
            } else {
                let input_file = &args[1];
                // extract suffix from input file
                let suffix = extract_suffix(input_file);
                let output_file = format!("../output/vampire_proof_{}.out", suffix);

                run_vamp::run_vampire_only(input_file, &output_file);
            }
        }
        _ => krympa::klog_error!(
            "Unknown command '{}'. Use 'collect', 'shorten', 'group', or 'minimize'",
            args[0]
        ),
    }
}
