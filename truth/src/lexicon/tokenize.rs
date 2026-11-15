//! The lexicon's deterministic tokenizer and rule-based English lemmatizer
//! (#1652). No NLP dependency: a fixed set of rules, documented in
//! `docs/lexicon.md`, with a lexicon entry's explicit `forms` taking
//! precedence over every rule.

/// One token of corpus prose that the lexicon must trace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    /// A word as written. `joined` is true when only whitespace separates it
    /// from the previous word, so a multi-word lemma may continue across it.
    Word { text: String, joined: bool },
    /// An upper snake case sense or term tag such as `PRIOR_1`; it is traced
    /// to its disambiguation, not to a lexicon entry.
    Tag(String),
}

fn is_hex_id(text: &str) -> bool {
    let mut digit = false;
    let ok = text.split('-').all(|part| {
        !part.is_empty()
            && part.chars().all(|c| {
                digit |= c.is_ascii_digit();
                c.is_ascii_hexdigit() && !c.is_ascii_uppercase()
            })
    });
    ok && digit
}

/// `[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`: a readable legacy id such as
/// `STMT-CATHOLICISM-TRUE`.
fn is_legacy_id(text: &str) -> bool {
    let mut parts = text.split('-');
    let first = parts.next().unwrap_or_default();
    let upper = |part: &str| {
        !part.is_empty()
            && part
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
    };
    let rest: Vec<&str> = parts.collect();
    first.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        && upper(first)
        && !rest.is_empty()
        && rest.iter().all(|part| upper(part))
}

/// `[A-Z][A-Z0-9_]*` containing `_`: a sense label (`PRIOR_1`) or term label.
fn is_tag(text: &str) -> bool {
    text.contains('_')
        && text.chars().next().is_some_and(|c| c.is_ascii_uppercase())
        && text
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
}

/// A lowercase letter directly followed by an uppercase one: a Lean or code
/// identifier (`hBridge`, `TruthCore`, `actualNonmutualOfDistinct`).
fn is_camel(text: &str) -> bool {
    let chars: Vec<char> = text.chars().collect();
    chars
        .windows(2)
        .any(|pair| pair[0].is_lowercase() && pair[1].is_uppercase())
}

/// `x.y` with letters or digits on both sides of an inner dot: a dotted Lean
/// name or a locator (`Profile.grounds`, `Theta.8`, `q.104`).
fn is_dotted(text: &str) -> bool {
    let chars: Vec<char> = text.chars().collect();
    chars
        .windows(3)
        .any(|w| w[1] == '.' && w[0].is_alphanumeric() && w[2].is_alphanumeric())
}

/// A dotted abbreviation with at least two letters, each followed by a dot
/// (`e.g.`, `i.e.`).
fn is_abbreviation(text: &str) -> bool {
    let chars: Vec<char> = text.chars().collect();
    chars.len() >= 4
        && chars.len().is_multiple_of(2)
        && chars
            .chunks(2)
            .all(|pair| pair[0].is_ascii_alphabetic() && pair[1] == '.')
}

/// Replaces every closed backtick code span by a space; an unmatched run of
/// backticks stays as punctuation.
fn blank_code(text: &str) -> String {
    let chars: Vec<char> = text.chars().collect();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < chars.len() {
        if chars[i] != '`' {
            out.push(chars[i]);
            i += 1;
            continue;
        }
        let mut run = 0;
        while i + run < chars.len() && chars[i + run] == '`' {
            run += 1;
        }
        let mut j = i + run;
        let mut close = None;
        while j < chars.len() {
            if chars[j] == '`' {
                let mut other = 0;
                while j + other < chars.len() && chars[j + other] == '`' {
                    other += 1;
                }
                if other == run {
                    close = Some(j + other);
                    break;
                }
                j += other;
            } else {
                j += 1;
            }
        }
        match close {
            Some(end) => {
                out.push_str(" \u{1} ");
                i = end;
            }
            None => {
                out.push(' ');
                i += run;
            }
        }
    }
    out
}

fn word_char(c: char) -> bool {
    c.is_alphanumeric() || matches!(c, '_' | '-' | '\'' | '\u{2019}' | '.')
}

/// The tokens of `text` that the lexicon traces, in order. Skipped: code
/// spans in backticks, URLs, uuids and hex id prefixes, legacy ids, dotted
/// names and locators, identifiers with an inner capital or underscore, any
/// token containing a digit, `#`/`@`/`$`/`\` references, and single letters
/// other than `a` and `I`.
pub fn tokenize(text: &str) -> Vec<Token> {
    let text = blank_code(text);
    let mut tokens = Vec::new();
    let mut joined = false;
    for chunk in text.split_whitespace() {
        if chunk.contains("://")
            || chunk
                .trim_start_matches(|c: char| !c.is_alphanumeric())
                .starts_with("www.")
        {
            joined = false;
            continue;
        }
        // Pieces: maximal runs of word characters, with the separator before.
        let chars: Vec<char> = chunk.chars().collect();
        let mut i = 0;
        while i < chars.len() {
            if !word_char(chars[i]) || (chars[i] == '.' && (i == 0 || !word_char(chars[i - 1]))) {
                joined = false;
                i += 1;
                continue;
            }
            let before = (i > 0).then(|| chars[i - 1]);
            let start = i;
            while i < chars.len() && word_char(chars[i]) {
                i += 1;
            }
            let raw: String = chars[start..i].iter().collect();
            let raw = raw.replace('\u{2019}', "'");
            let referenced = matches!(before, Some('#' | '@' | '$' | '\\'));
            emit(&raw, referenced, &mut joined, &mut tokens);
            if i < chars.len() {
                // Punctuation after a piece ends a phrase.
                joined = false;
            }
        }
    }
    tokens
}

fn emit(raw: &str, referenced: bool, joined: &mut bool, tokens: &mut Vec<Token>) {
    let abbreviation = raw.trim_start_matches(['\'', '-']);
    if is_abbreviation(abbreviation) {
        tokens.push(Token::Word {
            text: abbreviation.to_owned(),
            joined: false,
        });
        *joined = false;
        return;
    }
    let ended = raw.ends_with(['.', '\'', '-']) && !raw.ends_with("s'");
    let piece = raw.trim_matches(['.', '\'', '-']);
    let piece = if raw.ends_with("s'") {
        raw.trim_start_matches(['.', '\'', '-'])
            .trim_end_matches('.')
    } else {
        piece
    };
    let skip = piece.is_empty()
        || referenced
        || is_hex_id(piece)
        || is_legacy_id(piece)
        || piece.chars().any(char::is_numeric) && !is_tag(piece)
        || is_dotted(piece)
        || is_camel(piece)
        || (piece.contains('_') && !is_tag(piece))
        || (piece.chars().count() == 1 && !matches!(piece, "a" | "A" | "I"));
    if skip {
        *joined = false;
        return;
    }
    if is_tag(piece) {
        tokens.push(Token::Tag(piece.to_owned()));
        *joined = false;
        return;
    }
    tokens.push(Token::Word {
        text: piece.to_owned(),
        joined: *joined,
    });
    *joined = !ended;
}

/// The lowercase lookup key of a word: Unicode lowercase, typographic
/// apostrophe folded to `'`.
pub fn key(word: &str) -> String {
    word.replace('\u{2019}', "'").to_lowercase()
}

/// Candidate lemmas of a lowercase word, in the order the lemmatizer tries
/// them: possessive, plural, past and present participle rules. Only a
/// candidate of at least three characters is produced; a candidate counts
/// only when the lexicon has it, so the rules never invent a lemma.
pub fn candidates(word: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut push = |stem: &str, suffix: &str| {
        let candidate = format!("{stem}{suffix}");
        if candidate.chars().count() >= 3 && candidate != word && !out.contains(&candidate) {
            out.push(candidate);
        }
    };
    if let Some(stem) = word.strip_suffix("'s") {
        push(stem, "");
        return out;
    }
    if let Some(stem) = word.strip_suffix("s'") {
        push(stem, "");
        push(&format!("{stem}s"), "");
        return out;
    }
    let doubled = |stem: &str| {
        let chars: Vec<char> = stem.chars().collect();
        (chars.len() >= 2
            && chars[chars.len() - 1] == chars[chars.len() - 2]
            && !"aeiouls".contains(chars[chars.len() - 1]))
        .then(|| chars[..chars.len() - 1].iter().collect::<String>())
    };
    if let Some(stem) = word.strip_suffix("ies") {
        push(stem, "y");
    }
    if word.ends_with('s')
        && !word.ends_with("ss")
        && !word.ends_with("us")
        && !word.ends_with("is")
    {
        let stem = &word[..word.len() - 1];
        push(stem, "");
        if let Some(stem) = word.strip_suffix("es") {
            push(stem, "");
        }
        if let Some(stem) = word.strip_suffix("ves") {
            push(stem, "f");
            push(stem, "fe");
        }
    }
    if let Some(stem) = word.strip_suffix("ied") {
        push(stem, "y");
    }
    if let Some(stem) = word.strip_suffix("ed") {
        push(&format!("{stem}e"), "");
        push(stem, "");
        if let Some(single) = doubled(stem) {
            push(&single, "");
        }
    }
    if let Some(stem) = word.strip_suffix("ing") {
        push(stem, "");
        push(stem, "e");
        if let Some(single) = doubled(stem) {
            push(&single, "");
        }
        if let Some(stem) = stem.strip_suffix('y') {
            push(stem, "ie");
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(text: &str) -> Vec<String> {
        tokenize(text)
            .into_iter()
            .map(|token| match token {
                Token::Word { text, .. } => text,
                Token::Tag(tag) => format!("<{tag}>"),
            })
            .collect()
    }

    #[test]
    fn skips_code_ids_urls_numbers_and_identifiers() {
        assert_eq!(
            words(
                "The `foo bar` cause (see https://x.org/a.b) of STMT-CATHOLICISM-TRUE and 7a63a3fe."
            ),
            ["The", "cause", "see", "of", "and"]
        );
        assert_eq!(
            words(
                "0791f2ad-eeec-48b9-8f24-f2e711a5a2f9 hBridge TruthCore.Modal Theta.8 q.104 #1590 @codex x"
            ),
            Vec::<String>::new()
        );
        assert_eq!(words("definition_ids ``a `b` c`` done"), ["done"]);
        assert_eq!(words("a I A b"), ["a", "I", "A"]);
    }

    #[test]
    fn tags_abbreviations_hyphens_and_apostrophes() {
        assert_eq!(
            words("c is SIMPLY_PRIOR_1 to f, e.g. self-evident; Aquinas’ God's doesn't"),
            [
                "is",
                "<SIMPLY_PRIOR_1>",
                "to",
                "e.g.",
                "self-evident",
                "Aquinas'",
                "God's",
                "doesn't"
            ]
        );
        assert_eq!(words("PRIOR_1/PRIOR_2"), ["<PRIOR_1>", "<PRIOR_2>"]);
    }

    #[test]
    fn punctuation_breaks_phrases() {
        let joined: Vec<bool> = tokenize("per se, first cause (efficient) cause")
            .into_iter()
            .map(|token| matches!(token, Token::Word { joined: true, .. }))
            .collect();
        assert_eq!(joined, [false, true, false, true, false, false]);
    }

    #[test]
    fn lemmatizer_rules() {
        assert_eq!(candidates("causes")[0], "cause");
        assert!(candidates("boxes").contains(&"box".to_owned()));
        assert_eq!(candidates("bodies")[0], "body");
        assert_eq!(candidates("caused")[0], "cause");
        assert!(candidates("grounded").contains(&"ground".to_owned()));
        assert!(candidates("referred").contains(&"refer".to_owned()));
        assert!(candidates("causing").contains(&"cause".to_owned()));
        assert!(candidates("referring").contains(&"refer".to_owned()));
        assert_eq!(candidates("god's"), ["god"]);
        assert!(candidates("status").is_empty());
        assert!(
            !candidates("being").contains(&"be".to_owned()),
            "be is too short to be a candidate"
        );
        assert_eq!(key("Aquinas’"), "aquinas'");
    }
}
