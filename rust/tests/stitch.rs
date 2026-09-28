use krympa::{
    dag::build_dag, minimize::proof_uses_lemma, prover_wrapper::proof_succeeded, utils::*,
};
use std::{
    fs,
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "stitch-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        for sub in [
            "proofs/twee_tmp",
            "proofs/vampire_tmp",
            "lemmas/abstracted_stitch",
            "lemmas/small-step",
        ] {
            fs::create_dir_all(dir.join(sub)).unwrap();
        }
        Self(dir)
    }
    fn path(&self, sub: &str) -> String {
        self.0.join(sub).to_string_lossy().into_owned()
    }
    fn write(&self, sub: &str, text: &str) {
        fs::write(self.0.join(sub), text).unwrap();
    }
    fn stitch_winner(&self) {
        self.write("lemmas/abstracted_stitch/abstracted_stitch_lemma_0001.p", "fof(a1, axiom,\n ! [X0] : (op(X0,X0) = X0)\n).\nfof(conjecture_0001, conjecture,\n ! [Y0] : (op(Y0,Y0) = Y0)\n).\n");
        let proof = "RESULT: Theorem\nAxiom 1 (a1): op(X0,X0) = X0\nProof:\n= { by axiom 1 }\n";
        self.write("proofs/abstracted_stitch_lemma_0001_twee.proof", proof);
        self.write(
            "proofs/twee_tmp/abstracted_stitch_lemma_0001_twee.proof",
            proof,
        );
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn stitch_winner_resolves_loads_and_remains_in_dependency_dag() {
    let f = Fixture::new();
    f.stitch_winner();
    let proof = "RESULT: Theorem\nAxiom 1 (lemma_0001): op(X0,X0) = X0\nProof:\n= { by axiom 1 (lemma_0001) }\n";
    f.write("proofs/small_step_lemma_0002_twee.proof", proof);
    f.write("proofs/twee_tmp/small_step_lemma_0002_twee.proof", proof);
    f.write(
        "lemmas/small-step/small_step_lemma_0002.p",
        "fof(conjecture_0002, conjecture,\n ! [X0] : (op(op(X0,X0),X0) = X0)\n).\n",
    );
    let proofs = f.path("proofs");
    for name in ["lemma_0001", "abstracted_stitch_lemma_0001"] {
        assert_eq!(
            select_actual_lemma(&proofs, name).unwrap(),
            "abstracted_stitch_lemma_0001_twee"
        );
        assert_eq!(
            load_all_dependency_proofs(&proofs, &[name.into()])
                .unwrap()
                .len(),
            1
        );
    }
    let pc = precompute_lemmas(&proofs, &f.path("lemmas"), &f.path("proofs/twee_tmp")).unwrap();
    let (dag, _) = build_dag("small_step_lemma_0002", &pc).unwrap();
    assert!(dag["small_step_lemma_0002"].contains("abstracted_stitch_lemma_0001"));
    assert!(dag["abstracted_stitch_lemma_0001"].contains("a1"));
    assert!(proof_uses_lemma(
        "lemma_0001",
        &["Axiom 1 (abstracted_stitch_lemma_0001): op(X0,X0) = X0"]
    ));
}

#[test]
fn vampire_only_winner_retains_its_stitch_dependency() {
    let f = Fixture::new();
    f.stitch_winner();
    f.write("lemmas/small-step/small_step_lemma_0002.p", "fof(lemma_0001, lemma,\n ! [X0] : (op(X0,X0) = X0)\n).\nfof(conjecture_0002, conjecture,\n ! [X0] : (op(op(X0,X0),X0) = X0)\n).\n");
    f.write("proofs/small_step_lemma_0002_vampire.proof", "% SZS status Theorem\n1. ! [X0] : op(X0,X0) = X0 [input(assumption)]\n2. ! [X0] : op(op(X0,X0),X0) = X0 [input(conjecture)]\n3. $false [resolution 1,2]\n");
    let pc = precompute_lemmas(
        &f.path("proofs"),
        &f.path("lemmas"),
        &f.path("proofs/twee_tmp"),
    )
    .unwrap();
    assert_eq!(
        pc.all_lemmas["small_step_lemma_0002"].dependencies[0].0,
        "abstracted_stitch_lemma_0001"
    );
    let (dag, _) = build_dag("small_step_lemma_0002", &pc).unwrap();
    assert!(dag["small_step_lemma_0002"].contains("abstracted_stitch_lemma_0001"));
    f.write(
        "proofs/twee_tmp/small_step_lemma_0002_twee.proof",
        "RESULT: CounterSatisfiable",
    );
    assert!(precompute_lemmas(
        &f.path("proofs"),
        &f.path("lemmas"),
        &f.path("proofs/twee_tmp")
    )
    .is_ok());
    f.write(
        "proofs/small_step_lemma_0002_vampire.proof",
        "% SZS status Theorem\n1. unknown(X0) [input(assumption)]\n",
    );
    assert!(precompute_lemmas(
        &f.path("proofs"),
        &f.path("lemmas"),
        &f.path("proofs/twee_tmp")
    )
    .is_err());
}

#[test]
fn only_explicit_success_statuses_are_proofs() {
    for text in [
        "",
        "% SZS status Unknown",
        "RESULT: CounterSatisfiable",
        "% SZS status Timeout",
        "RESULT: Satisfiable",
    ] {
        assert!(!proof_succeeded(text));
    }
    for text in [
        "% SZS status Theorem for test",
        "RESULT: Theorem (the conjecture is true).",
        "% SZS status Unsatisfiable",
    ] {
        assert!(proof_succeeded(text));
    }
    assert!(is_builtin_axiom("a1"));
    assert!(is_builtin_axiom("a_23"));
    assert!(!is_builtin_axiom("abstracted_lemma_0001"));
    assert!(!is_builtin_axiom("abstracted_stitch_lemma_0001"));
}

#[test]
#[cfg(unix)]
fn shorten_reuses_a_forced_stitch_winner_and_cli_reports_minimize_errors() {
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;
    let f = Fixture::new();
    f.stitch_winner();
    for dir in ["rust", "bin", "output"] {
        fs::create_dir_all(f.0.join(dir)).unwrap();
    }
    for prover in ["vampire", "twee"] {
        let script = f.0.join("bin").join(prover);
        fs::write(
            &script,
            "#!/bin/sh\necho 'RESULT: Theorem'\necho 'Proof:'\necho '= { by axiom 1 }'\n",
        )
        .unwrap();
        fs::set_permissions(&script, fs::Permissions::from_mode(0o755)).unwrap();
    }
    f.write("lemmas/small-step/small_step_lemma_0002.p", "fof(lemma_0001, lemma,\n ! [X0] : (op(op(X0,X0),op(X0,X0)) = op(X0,X0))\n).\nfof(conjecture_0002, conjecture,\n ! [X0] : (op(op(X0,X0),X0) = X0)\n).\n");
    f.write("output/summary_test.json", r#"{"1":["abstracted_stitch_lemma_0001","twee",""],"2":["small_step_lemma_0002","twee",""]}"#);
    let result = Command::new(env!("CARGO_BIN_EXE_krympa"))
        .args(["shorten", "test.p"])
        .current_dir(f.0.join("rust"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let problem =
        fs::read_to_string(f.0.join("lemmas/small-step/small_step_lemma_0002.p")).unwrap();
    assert!(problem.contains("! [Y0] : (op(Y0,Y0) = Y0)"));
    assert!(!problem.contains("op(op(X0,X0),op(X0,X0))"));
    let result = Command::new(env!("CARGO_BIN_EXE_krympa"))
        .args(["minimize", "missing.p"])
        .current_dir(f.0.join("rust"))
        .output()
        .unwrap();
    assert!(!result.status.success());
}
