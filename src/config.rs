//! Typort.toml project configuration (veryl's Veryl.toml pattern).
//!
//! A project is the directory tree rooted at the Typort.toml. `[project]`
//! names it and points at the sources; `[build]` configures artifact
//! output (`typort build`); `[test]` configures simulation (`typort test`).
//! CLI flags override config values. Unknown fields are rejected so typos
//! surface immediately.

use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;

use crate::sim::Simulator;

pub const CONFIG_FILE: &str = "Typort.toml";

#[derive(Debug)]
pub enum ConfigError {
    /// No Typort.toml in this directory or any parent.
    NotFound(PathBuf),
    Io(std::io::Error),
    Parse(String),
}

impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConfigError::NotFound(from) => {
                write!(f, "no {CONFIG_FILE} found in {} or any parent", from.display())
            }
            ConfigError::Io(e) => write!(f, "{e}"),
            ConfigError::Parse(msg) => write!(f, "invalid {CONFIG_FILE}: {msg}"),
        }
    }
}

impl std::error::Error for ConfigError {}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub project: Project,
    #[serde(default)]
    pub build: Build,
    #[serde(default)]
    pub test: Test,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Project {
    pub name: String,
    /// Source files and/or directories (scanned recursively for .typort),
    /// relative to the Typort.toml directory. Defaults to the project root.
    #[serde(default)]
    pub sources: Vec<String>,
    /// Default top module instantiation ("top" or "adder[8]").
    pub top: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Build {
    /// Artifact directory, relative to the project root.
    #[serde(default = "default_target")]
    pub target: String,
}

impl Default for Build {
    fn default() -> Self {
        // Field-level serde defaults don't apply when the whole section is
        // absent (Config's #[serde(default)] calls this instead).
        Build { target: default_target() }
    }
}

fn default_target() -> String {
    "target_typort".to_string()
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Test {
    /// Simulation backend: verilator (default), icarus, vcs, vivado.
    #[serde(default = "default_simulator")]
    pub simulator: Simulator,
    /// Compile the model with VCD tracing.
    #[serde(default)]
    pub trace: bool,
    #[serde(default)]
    pub verilator: Verilator,
}

impl Default for Test {
    fn default() -> Self {
        Test {
            simulator: default_simulator(),
            trace: false,
            verilator: Verilator::default(),
        }
    }
}

fn default_simulator() -> Simulator {
    Simulator::Verilator
}

#[derive(Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Verilator {
    #[serde(default)]
    pub compile_args: Vec<String>,
}

/// A discovered project: the parsed config plus its root directory (the
/// Typort.toml's parent), which source paths and target dirs resolve against.
#[derive(Debug)]
pub struct ProjectConfig {
    pub config: Config,
    pub root: PathBuf,
}

impl Config {
    pub fn load_from(path: &Path) -> Result<Config, ConfigError> {
        let text = fs::read_to_string(path).map_err(ConfigError::Io)?;
        toml::from_str(&text).map_err(|e| ConfigError::Parse(e.to_string()))
    }

    /// Find the nearest Typort.toml at `from` or above it.
    pub fn discover(from: &Path) -> Result<ProjectConfig, ConfigError> {
        let mut dir = Some(from.to_path_buf());
        while let Some(d) = dir {
            let candidate = d.join(CONFIG_FILE);
            if candidate.is_file() {
                let config = Config::load_from(&candidate)?;
                return Ok(ProjectConfig { config, root: d });
            }
            dir = d.parent().map(|p| p.to_path_buf());
        }
        Err(ConfigError::NotFound(from.to_path_buf()))
    }
}

impl ProjectConfig {
    /// Resolve the configured sources into a deterministic (sorted) list of
    /// .typort file paths. Directories are walked recursively; files are
    /// taken as-is.
    pub fn collect_sources(&self) -> Result<Vec<PathBuf>, ConfigError> {
        let entries: Vec<&String> = if self.config.project.sources.is_empty() {
            // No sources configured: the project root itself.
            vec![]
        } else {
            self.config.project.sources.iter().collect()
        };
        let roots: Vec<PathBuf> = entries
            .iter()
            .map(|s| self.root.join(s))
            .collect();
        let effective: Vec<PathBuf> = if roots.is_empty() {
            vec![self.root.clone()]
        } else {
            roots
        };
        let mut files = Vec::new();
        for root in effective {
            if root.is_dir() {
                for entry in walkdir::WalkDir::new(&root)
                    .into_iter()
                    .filter_map(|e| e.ok())
                {
                    let p = entry.path();
                    if p.extension().map(|e| e == "typort").unwrap_or(false) {
                        files.push(p.to_path_buf());
                    }
                }
            } else if root.is_file() {
                files.push(root);
            } else {
                return Err(ConfigError::Io(std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    format!("source path {} does not exist", root.display()),
                )));
            }
        }
        files.sort();
        files.dedup();
        Ok(files)
    }

    /// Artifact output directory (created).
    pub fn target_dir(&self) -> PathBuf {
        self.root.join(&self.config.build.target)
    }
}
