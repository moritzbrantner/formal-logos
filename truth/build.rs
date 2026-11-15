//! Fingerprints the truth crate's sources as `TRUTH_PRODUCER_SHA256`, the
//! producer provenance that generated artifacts (the structure report)
//! record and their freshness checks require: an artifact written by other
//! Rust code is stale even when every corpus, Lean and script input matches.

#[path = "src/sha256.rs"]
mod sha256;

use std::{
    fs,
    path::{Path, PathBuf},
};

fn sources(directory: &Path, found: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
        .map(|entry| entry.expect("directory entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            sources(&path, found);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            found.push(path);
        }
    }
}

fn main() {
    let crate_root = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("manifest dir"));
    // The crate's own sources and manifest, its build script and the
    // workspace lock file (the dependency versions it is built with).
    let mut inputs = vec![
        (crate_root.join("Cargo.toml"), "truth/Cargo.toml".to_owned()),
        (crate_root.join("build.rs"), "truth/build.rs".to_owned()),
        (crate_root.join("../Cargo.lock"), "Cargo.lock".to_owned()),
    ];
    let mut found = Vec::new();
    sources(&crate_root.join("src"), &mut found);
    for path in found {
        let name = path
            .strip_prefix(&crate_root)
            .expect("crate source")
            .to_string_lossy()
            .replace('\\', "/");
        inputs.push((path, format!("truth/{name}")));
    }
    let mut manifest = String::new();
    for (path, name) in &inputs {
        let bytes = fs::read(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        manifest.push_str(&format!("{name}\t{}\n", sha256::sha256_hex(&bytes)));
    }
    println!(
        "cargo:rustc-env=TRUTH_PRODUCER_SHA256={}",
        sha256::sha256_hex(manifest.as_bytes())
    );
    for watched in ["src", "Cargo.toml", "build.rs", "../Cargo.lock"] {
        println!("cargo:rerun-if-changed={watched}");
    }
}
