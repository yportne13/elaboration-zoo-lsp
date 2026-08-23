// Typort.toml config parsing/discovery and the `typort build` / `typort
// test` project commands (driven through the real binary via
// CARGO_BIN_EXE_typort).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use elaboration_zoo_lsp::config::Config;
use elaboration_zoo_lsp::sim::Simulator;

fn temp_project(tag: &str, files: &[(&str, &str)]) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("typort-config-tests-{}-{tag}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    for (name, content) in files {
        let path = dir.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, content).unwrap();
    }
    dir
}

#[test]
fn parses_all_sections() {
    let dir = temp_project(
        "parse",
        &[(
            "Typort.toml",
            r#"
[project]
name = "demo"
sources = ["src", "lib/extra.typort"]
top = "adder[8]"

[build]
target = "out"

[test]
simulator = "verilator"
trace = true

[test.verilator]
compile_args = ["-Wno-lint"]
"#,
        )],
    );
    let cfg = Config::load_from(&dir.join("Typort.toml")).unwrap();
    assert_eq!(cfg.project.name, "demo");
    assert_eq!(cfg.project.sources, vec!["src", "lib/extra.typort"]);
    assert_eq!(cfg.project.top.as_deref(), Some("adder[8]"));
    assert_eq!(cfg.build.target, "out");
    assert_eq!(cfg.test.simulator, Simulator::Verilator);
    assert!(cfg.test.trace);
    assert_eq!(cfg.test.verilator.compile_args, vec!["-Wno-lint"]);
}

#[test]
fn simulator_field_parses_and_rejects() {
    let ok = temp_project(
        "sim-parse",
        &[(
            "Typort.toml",
            "[project]\nname = \"demo\"\n\n[test]\nsimulator = \"icarus\"\n",
        )],
    );
    let cfg = Config::load_from(&ok.join("Typort.toml")).unwrap();
    assert_eq!(cfg.test.simulator, Simulator::Icarus);

    let bad = temp_project(
        "sim-typo",
        &[(
            "Typort.toml",
            "[project]\nname = \"demo\"\n\n[test]\nsimulator = \"vera\"\n",
        )],
    );
    let err = Config::load_from(&bad.join("Typort.toml")).unwrap_err();
    assert!(err.to_string().contains("invalid Typort.toml"), "got: {err}");
}

#[test]
fn defaults_and_unknown_fields() {
    let dir = temp_project(
        "defaults",
        &[(
            "Typort.toml",
            r#"
[project]
name = "demo"
"#,
        )],
    );
    let cfg = Config::load_from(&dir.join("Typort.toml")).unwrap();
    assert!(cfg.project.sources.is_empty());
    assert!(cfg.project.top.is_none());
    assert_eq!(cfg.build.target, "target_typort");
    assert_eq!(cfg.test.simulator, Simulator::Verilator);
    assert!(!cfg.test.trace);

    let dir = temp_project(
        "typo",
        &[(
            "Typort.toml",
            r#"
[project]
name = "demo"
sourcse = ["src"]
"#,
        )],
    );
    let err = Config::load_from(&dir.join("Typort.toml")).unwrap_err();
    assert!(err.to_string().contains("invalid Typort.toml"), "got: {err}");
}

#[test]
fn discover_walks_up_and_collects_sources() {
    let dir = temp_project(
        "discover",
        &[
            ("Typort.toml", "[project]\nname = \"demo\"\ntop = \"smoke\"\n"),
            ("src/a.typort", "module smokeA {}\n"),
            ("src/nested/b.typort", "module smokeB {}\n"),
            ("lib/extra.typort", "module smokeC {}\n"),
        ],
    );
    // Discover from a nested subdir: must find the root's Typort.toml.
    let project = Config::discover(&dir.join("src/nested")).unwrap();
    assert_eq!(project.root, dir);

    // No sources configured: walk the project root.
    let walked = project.collect_sources().unwrap();
    assert_eq!(
        walked,
        vec![
            dir.join("lib/extra.typort"),
            dir.join("src/a.typort"),
            dir.join("src/nested/b.typort"),
        ]
    );

    // Missing config above temp dir root: NotFound (use a fresh empty dir).
    let empty = temp_project("empty", &[]);
    let err = Config::discover(&empty).unwrap_err();
    // The walk-up may still find a Typort.toml in %TEMP% parents — only
    // assert NotFound when the parents are clean, so just check it's an
    // error variant name, not a panic.
    let _ = match err {
        e @ elaboration_zoo_lsp::config::ConfigError::NotFound(_) => e,
        other => panic!("expected NotFound, got {other}"),
    };
}

const SMOKE_TYPORT: &str = r#"
[project]
name = "smoke-proj"
top = "smoke"

[build]
target = "out"
"#;

const SMOKE_SRC: &str = r#"
module smoke {
    input a = UInt[8]
    output y = UInt[8]
    y := a
}
"#;

fn typort_bin() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_typort"));
    cmd.stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped());
    cmd
}

#[test]
fn build_command_emits_artifacts() {
    let dir = temp_project(
        "build",
        &[
            ("Typort.toml", SMOKE_TYPORT),
            ("src/smoke.typort", SMOKE_SRC),
        ],
    );
    // Run from a NESTED dir: config discovery must resolve the root.
    let out = typort_bin()
        .current_dir(dir.join("src"))
        .args(["build"])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "typort build failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );

    let target = dir.join("out");
    let verilog = fs::read_to_string(target.join("smoke.v")).unwrap();
    assert!(verilog.contains("module smoke"), "in:\n{verilog}");
    let manifest = fs::read_to_string(target.join("smoke.manifest.json")).unwrap();
    assert!(manifest.contains("\"top\": \"smoke\""));
    let filelist = fs::read_to_string(target.join("smoke-proj.f")).unwrap();
    assert_eq!(filelist, "smoke.v\n");
}

#[test]
fn build_requires_top() {
    let dir = temp_project(
        "no-top",
        &[
            ("Typort.toml", "[project]\nname = \"demo\"\n"),
            ("src/smoke.typort", SMOKE_SRC),
        ],
    );
    let out = typort_bin().current_dir(&dir).args(["build"]).output().unwrap();
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("no top module"), "got: {stderr}");
}

#[test]
fn test_command_smoke_runs_model() {
    if elaboration_zoo_lsp::sim::find_verilator().is_none() {
        eprintln!("[SKIP] verilator not found — typort test integration unavailable");
        return;
    }
    let dir = temp_project(
        "test",
        &[
            ("Typort.toml", SMOKE_TYPORT),
            ("src/smoke.typort", SMOKE_SRC),
        ],
    );
    let out = typort_bin().current_dir(&dir).args(["test"]).output().unwrap();
    assert!(
        out.status.success(),
        "typort test failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("ok: smoke model compiled"), "got: {stdout}");
    assert!(dir.join("out/sim_smoke/obj_smoke").is_dir());
}
