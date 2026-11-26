use crate::notes;
use serde::Serialize;
use std::{collections::BTreeMap, fs, path::Path};

/// Repeated headings, short pointers, quotations and sample code occur
/// deliberately throughout the notes. Count authored prose to select sections,
/// then compare their entire bodies, including any quotes and code.
const MIN_PROSE_WORDS: usize = 50;

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct NoteOccurrence {
    pub path: String,
    pub line: usize,
    pub heading: String,
}

fn substantial_prose(body: &str) -> bool {
    let mut words = 0;
    let mut open_fence = None;
    let mut in_quote = false;
    for line in body.lines() {
        let trimmed = line.trim_start();
        if trimmed.is_empty() {
            in_quote = false;
            continue;
        }
        if let Some((marker, length)) = open_fence {
            if notes::fence(line).is_some_and(|(m, n)| m == marker && n >= length) {
                open_fence = None;
            }
            continue;
        }
        if trimmed.starts_with('>') {
            in_quote = true;
        }
        if in_quote {
            continue;
        }
        open_fence = notes::fence(line);
        if open_fence.is_some() || line.starts_with("    ") || line.starts_with('\t') {
            continue;
        }
        words += line.split_whitespace().count();
        if words >= MIN_PROSE_WORDS {
            return true;
        }
    }
    false
}

/// Exact matches among complete indexed Markdown sections, within and across
/// files. Read the notes directly so this check works without a corpus cache.
pub fn duplicate_note_sections(root: &Path) -> Result<Vec<Vec<NoteOccurrence>>, String> {
    let mut by_body = BTreeMap::<String, Vec<NoteOccurrence>>::new();
    for path in notes::inputs(root)? {
        let text = fs::read_to_string(root.join(&path)).map_err(|e| format!("{path}: {e}"))?;
        for section in notes::parse(&path, &text).sections {
            let body = section.body.trim_matches('\n');
            if section.heading == "Research attempts citing this note" || !substantial_prose(body) {
                continue;
            }
            by_body
                .entry(body.to_owned())
                .or_default()
                .push(NoteOccurrence {
                    path: path.clone(),
                    line: section.line,
                    heading: section.heading,
                });
        }
    }
    let mut groups: Vec<_> = by_body.into_values().filter(|g| g.len() > 1).collect();
    groups.sort_unstable();
    Ok(groups)
}
