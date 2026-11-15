//! Key-order-preserving JSON for the commands that print or rewrite a record
//! as Python's `json.dumps(json.loads(raw), ensure_ascii=False, indent=…)`
//! does: `serde_json` (without `preserve_order`) sorts object keys, Python
//! keeps file order. Numbers and strings are re-emitted the way Python's
//! encoder writes them.

use serde::de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};
use std::fmt;

/// A JSON value whose objects keep their keys in file order.
#[derive(Clone, Debug, PartialEq)]
pub enum Ordered {
    Null,
    Bool(bool),
    Int(i128),
    Float(f64),
    String(String),
    Array(Vec<Ordered>),
    /// Keys in first-seen order; a repeated key keeps its first position and
    /// its last value, as a Python `dict` built by `json.loads` does.
    Object(Vec<(String, Ordered)>),
}

impl Ordered {
    /// Parses `text` (Python `json.loads`).
    pub fn parse(text: &str) -> Result<Self, String> {
        serde_json::from_str(text).map_err(|error| error.to_string())
    }

    /// The value of `key` in an object.
    pub fn get(&self, key: &str) -> Option<&Ordered> {
        match self {
            Ordered::Object(entries) => entries
                .iter()
                .find(|(name, _)| name == key)
                .map(|(_, value)| value),
            _ => None,
        }
    }

    /// The mutable value of `key` in an object.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut Ordered> {
        match self {
            Ordered::Object(entries) => entries
                .iter_mut()
                .find(|(name, _)| name == key)
                .map(|(_, value)| value),
            _ => None,
        }
    }

    /// Python `json.dumps(value, ensure_ascii=False, indent=indent)`.
    pub fn dumps(&self, indent: Option<usize>) -> String {
        let mut out = String::new();
        self.write(&mut out, indent, 0);
        out
    }

    fn write(&self, out: &mut String, indent: Option<usize>, level: usize) {
        match self {
            Ordered::Null => out.push_str("null"),
            Ordered::Bool(value) => out.push_str(if *value { "true" } else { "false" }),
            Ordered::Int(value) => out.push_str(&value.to_string()),
            Ordered::Float(value) => out.push_str(&float_repr(*value)),
            Ordered::String(text) => write_string(out, text),
            Ordered::Array(items) => {
                if items.is_empty() {
                    out.push_str("[]");
                    return;
                }
                out.push('[');
                for (index, item) in items.iter().enumerate() {
                    separator(out, indent, level + 1, index == 0);
                    item.write(out, indent, level + 1);
                }
                close(out, indent, level);
                out.push(']');
            }
            Ordered::Object(entries) => {
                if entries.is_empty() {
                    out.push_str("{}");
                    return;
                }
                out.push('{');
                for (index, (key, value)) in entries.iter().enumerate() {
                    separator(out, indent, level + 1, index == 0);
                    write_string(out, key);
                    out.push_str(": ");
                    value.write(out, indent, level + 1);
                }
                close(out, indent, level);
                out.push('}');
            }
        }
    }
}

fn separator(out: &mut String, indent: Option<usize>, level: usize, first: bool) {
    match indent {
        Some(width) => {
            if !first {
                out.push(',');
            }
            out.push('\n');
            out.push_str(&" ".repeat(width * level));
        }
        None if !first => out.push_str(", "),
        None => {}
    }
}

fn close(out: &mut String, indent: Option<usize>, level: usize) {
    if let Some(width) = indent {
        out.push('\n');
        out.push_str(&" ".repeat(width * level));
    }
}

/// Python's `ensure_ascii=False` string encoder.
fn write_string(out: &mut String, text: &str) {
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\x08' => out.push_str("\\b"),
            '\x0c' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Python `float.__repr__`: the shortest round-trip digits, in exponent form
/// when the decimal exponent is below -4 or at least 16.
fn float_repr(value: f64) -> String {
    if value.is_nan() {
        return "NaN".into();
    }
    if value.is_infinite() {
        return if value > 0.0 { "Infinity" } else { "-Infinity" }.into();
    }
    // `{:e}` gives the shortest round-trip mantissa: "1.5e-7", "-1e20".
    let scientific = format!("{value:e}");
    let (mantissa, exponent) = scientific.split_once('e').unwrap_or((&scientific, "0"));
    let exponent: i32 = exponent.parse().unwrap_or(0);
    if (-4..16).contains(&exponent) {
        let plain = format!("{value}");
        if plain.contains('.') {
            plain
        } else {
            format!("{plain}.0")
        }
    } else {
        let sign = if exponent < 0 { '-' } else { '+' };
        format!("{mantissa}e{sign}{:02}", exponent.abs())
    }
}

impl<'de> Deserialize<'de> for Ordered {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(OrderedVisitor)
    }
}

struct OrderedVisitor;

impl<'de> Visitor<'de> for OrderedVisitor {
    type Value = Ordered;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a JSON value")
    }

    fn visit_unit<E: de::Error>(self) -> Result<Ordered, E> {
        Ok(Ordered::Null)
    }

    fn visit_bool<E: de::Error>(self, value: bool) -> Result<Ordered, E> {
        Ok(Ordered::Bool(value))
    }

    fn visit_i64<E: de::Error>(self, value: i64) -> Result<Ordered, E> {
        Ok(Ordered::Int(value.into()))
    }

    fn visit_u64<E: de::Error>(self, value: u64) -> Result<Ordered, E> {
        Ok(Ordered::Int(value.into()))
    }

    fn visit_f64<E: de::Error>(self, value: f64) -> Result<Ordered, E> {
        Ok(Ordered::Float(value))
    }

    fn visit_str<E: de::Error>(self, value: &str) -> Result<Ordered, E> {
        Ok(Ordered::String(value.to_owned()))
    }

    fn visit_string<E: de::Error>(self, value: String) -> Result<Ordered, E> {
        Ok(Ordered::String(value))
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Ordered, A::Error> {
        let mut items = Vec::new();
        while let Some(item) = seq.next_element()? {
            items.push(item);
        }
        Ok(Ordered::Array(items))
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Ordered, A::Error> {
        let mut entries: Vec<(String, Ordered)> = Vec::new();
        // Key positions, so a large object (a hashed input manifest) loads
        // in linear time.
        let mut positions: std::collections::HashMap<String, usize> =
            std::collections::HashMap::new();
        while let Some((key, value)) = map.next_entry::<String, Ordered>()? {
            match positions.get(&key) {
                Some(&index) => entries[index].1 = value,
                None => {
                    positions.insert(key.clone(), entries.len());
                    entries.push((key, value));
                }
            }
        }
        Ok(Ordered::Object(entries))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dumps_like_python() {
        let value = Ordered::parse(
            r#"{"z": [1, 2.5, 1e20, 1e-7, 3.0], "a": {"k": "é\"\n\u0001"}, "e": [], "o": {}, "z": [true, null]}"#,
        )
        .unwrap();
        assert_eq!(
            value.dumps(None),
            r#"{"z": [true, null], "a": {"k": "é\"\n\u0001"}, "e": [], "o": {}}"#
        );
        assert_eq!(
            value.dumps(Some(2)),
            "{\n  \"z\": [\n    true,\n    null\n  ],\n  \"a\": {\n    \"k\": \"é\\\"\\n\\u0001\"\n  },\n  \"e\": [],\n  \"o\": {}\n}"
        );
        let numbers =
            Ordered::parse("[1, 2.5, 1e20, 1e-7, 3.0, 1e16, 123456789012345.6, 0.0001]").unwrap();
        assert_eq!(
            numbers.dumps(None),
            "[1, 2.5, 1e+20, 1e-07, 3.0, 1e+16, 123456789012345.6, 0.0001]"
        );
    }
}
