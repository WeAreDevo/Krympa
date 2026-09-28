use krympa::bench_run::run;
use krympa::execution::{parse_execution_options, set_execution_mode, set_term_size_aware};
use std::env;

fn main() {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    let (mode, tsa, args) = match parse_execution_options(&raw_args) {
        Ok(parsed) => parsed,
        Err(err) => {
            krympa::klog_error!("{}", err);
            std::process::exit(1);
        }
    };

    if let Err(err) = set_execution_mode(mode) {
        krympa::klog_error!("{}", err);
        std::process::exit(1);
    }

    set_term_size_aware(tsa);

    if args.len() < 2 {
        krympa::klog_error!(
            "Usage: benchmarking [--parallel|--sequential] [--term-size] <input_folder> <timeout_secs> [krympa_binary]"
        );
        std::process::exit(1);
    }

    let input_folder = &args[0];
    let timeout_secs: u64 = args[1].parse().expect("timeout_secs must be a number");

    let krympa_bin = if args.len() >= 3 {
        &args[2]
    } else {
        "./krympa"
    };

    run(input_folder, krympa_bin, timeout_secs, mode);
}
