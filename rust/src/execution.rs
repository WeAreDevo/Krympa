use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionMode {
    Parallel,
    Sequential,
}

impl ExecutionMode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Parallel => "parallel",
            Self::Sequential => "sequential",
        }
    }

    pub fn cli_flag(self) -> &'static str {
        match self {
            Self::Parallel => "--parallel",
            Self::Sequential => "--sequential",
        }
    }

    fn from_value(value: &str) -> Result<Self, String> {
        match value {
            "parallel" => Ok(Self::Parallel),
            "sequential" => Ok(Self::Sequential),
            _ => Err(format!(
                "Unknown execution mode '{}'. Use 'parallel' or 'sequential'.",
                value
            )),
        }
    }
}

static EXECUTION_MODE: OnceLock<ExecutionMode> = OnceLock::new();

pub fn execution_mode() -> ExecutionMode {
    *EXECUTION_MODE.get_or_init(|| ExecutionMode::Parallel)
}

pub fn set_execution_mode(mode: ExecutionMode) -> Result<(), String> {
    if let Some(existing) = EXECUTION_MODE.get() {
        if *existing == mode {
            return Ok(());
        }

        return Err(format!(
            "Execution mode already set to '{}', cannot switch to '{}'.",
            existing.as_str(),
            mode.as_str()
        ));
    }

    EXECUTION_MODE
        .set(mode)
        .map_err(|_| "Failed to initialize execution mode.".to_string())
}

pub fn parse_execution_mode_args(args: &[String]) -> Result<(ExecutionMode, Vec<String>), String> {
    let mut mode = ExecutionMode::Parallel;
    let mut positionals = Vec::new();
    let mut idx = 0;

    while idx < args.len() {
        match args[idx].as_str() {
            "--parallel" => mode = ExecutionMode::Parallel,
            "--sequential" => mode = ExecutionMode::Sequential,
            "--execution-mode" => {
                let value = args
                    .get(idx + 1)
                    .ok_or("Missing value after --execution-mode".to_string())?;
                mode = ExecutionMode::from_value(value)?;
                idx += 1;
            }
            arg if arg.starts_with("--execution-mode=") => {
                let value = arg.trim_start_matches("--execution-mode=");
                mode = ExecutionMode::from_value(value)?;
            }
            _ => positionals.push(args[idx].clone()),
        }
        idx += 1;
    }

    Ok((mode, positionals))
}
