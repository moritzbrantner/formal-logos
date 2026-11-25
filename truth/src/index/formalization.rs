//! Locate formal work embedded in the documentation for migration to Lean.
use crate::notes;
use serde::Serialize;
use std::{fs, path::Path};

#[derive(Debug, Serialize)]
pub struct Candidate {
    pub path: String,
    pub line: usize,
    pub language: String,
    pub kind: &'static str,
}

fn classify(language: &str, body: &str) -> Option<&'static str> {
    if language == "lean" || language == "lean4" {
        let declaration = body.lines().any(|line| {
            let mut tokens = line.split_whitespace();
            matches!(
                tokens.find(|word| !matches!(
                    *word,
                    "private" | "protected" | "public" | "noncomputable"
                )),
                Some("theorem" | "lemma" | "example")
            )
        });
        return (declaration && body.contains(":=")).then_some("lean_proof");
    }
    let checked = match language {
        "python" | "python3" => body
            .lines()
            .any(|line| line.trim_start().starts_with("assert ")),
        "js" | "javascript" | "ts" | "typescript" => {
            body.contains("assert") || body.contains("throw new Error")
        }
        _ => false,
    };
    checked.then_some("executable_comparison")
}

/// Reports both kinds with locations; an executable comparison may be an IO,
/// historical replay or regression fixture rather than a mathematical claim.
pub fn candidates(root: &Path) -> Result<Vec<Candidate>, String> {
    let mut rows = Vec::new();
    for path in notes::inputs(root)? {
        let text = fs::read_to_string(root.join(&path)).map_err(|e| format!("{path}: {e}"))?;
        let mut lines = text.lines().enumerate();
        while let Some((start, line)) = lines.next() {
            let Some((marker, width)) = notes::fence(line) else {
                continue;
            };
            let language = line.trim_start()[width..]
                .split_whitespace()
                .next()
                .unwrap_or_default();
            let mut body = String::new();
            for (_, content) in lines.by_ref() {
                if notes::fence(content).is_some_and(|(m, n)| {
                    m == marker && n >= width && content.trim().chars().all(|c| c == marker)
                }) {
                    break;
                }
                body.push_str(content);
                body.push('\n');
            }
            if let Some(kind) = classify(language, &body) {
                rows.push(Candidate {
                    path: path.clone(),
                    line: start + 1,
                    language: language.to_owned(),
                    kind,
                });
            }
        }
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::classify;
    #[test]
    fn distinguishes_proofs_from_source_queries_and_calculation_fixtures() {
        assert_eq!(
            classify("lean", "private theorem p : True := by trivial"),
            Some("lean_proof")
        );
        assert_eq!(classify("lean", "#check True.intro"), None);
        assert_eq!(classify("lean", "theorem p : True"), None);
        assert_eq!(
            classify("python", "assert count == 80"),
            Some("executable_comparison")
        );
        assert_eq!(classify("sh", "lake build"), None);
    }
}
