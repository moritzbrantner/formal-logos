//! `truth index`: the disposable SQLite/FTS5 lookup projection of the corpus
//! (#954 slice B7), ported from `scripts/research_index.py`.
//!
//! The JSON corpus stays authoritative. The index is a cache: it is stored
//! under `.cache/`, bound to an FNV-1a digest of every indexed path and byte
//! (the hash behind [`crate::Corpus::input_identity`], extended to every
//! `corpus/**/*.json` file the projection reads) and to [`BUILDER`], and it is
//! rebuilt whenever that binding is stale. Publication is atomic: a failed
//! build leaves the previous database in place. Nothing here certifies a
//! proof, closes a premise or changes a route.
//!
//! The tables, the record projection (nested passages included), the search
//! expression and every query are Python's, so rows and FTS5 `bm25` ranks
//! match on the same inputs (rows are inserted in Python's path order, which
//! also fixes the order of equal ranks).

use crate::{
    FNV1A64_OFFSET,
    configurations::{self, Index},
    fnv1a64_update,
    identity::{Aliases, Unresolved},
    pyfmt,
    pyjson::float_repr,
};
use rusqlite::{Connection, OpenFlags, OptionalExtension, params};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::{SystemTime, UNIX_EPOCH},
};

type Obj = Map<String, Value>;

/// The table layout (`research_index.SCHEMA`).
pub const SCHEMA: &str = "3";
/// The projection semantics; bump it when a change must invalidate every
/// existing index.
pub const BUILDER: &str = "truth-index-1";
/// The database, relative to the checkout. Python's projection lives in
/// `.cache/research-index.sqlite`; separate files keep the two from
/// invalidating each other.
pub const PATH: &str = ".cache/truth-index.sqlite";

const TABLES: &str = "
    CREATE TABLE metadata(key TEXT PRIMARY KEY, value TEXT NOT NULL);
    CREATE TABLE source_files(path TEXT PRIMARY KEY, content BLOB NOT NULL);
    CREATE TABLE records(key TEXT PRIMARY KEY, id TEXT, kind TEXT, path TEXT, body TEXT);
    CREATE INDEX records_id ON records(id);
    CREATE TABLE refs(owner TEXT, target TEXT, PRIMARY KEY(owner,target));
    CREATE INDEX refs_target ON refs(target);
    CREATE TABLE arguments(id TEXT PRIMARY KEY, signature TEXT, conclusion TEXT);
    CREATE INDEX argument_signature ON arguments(signature,conclusion);
    CREATE VIRTUAL TABLE search USING fts5(id UNINDEXED, text, tokenize='unicode61');
";

pub type Result<T> = std::result::Result<T, String>;

fn sql(error: rusqlite::Error) -> String {
    error.to_string()
}

/// The database path of the checkout at `root`.
pub fn database(root: &Path) -> PathBuf {
    root.join(PATH)
}

/// Every `corpus/**/*.json` path, relative to `root`, in Python's
/// `sorted(Path.rglob('*.json'))` order (part by part). Symlinked directories
/// are not entered, as `rglob` does not.
pub fn inputs(root: &Path) -> Result<Vec<String>> {
    fn walk(directory: &Path, parts: &mut Vec<String>, out: &mut Vec<Vec<String>>) -> Result<()> {
        let entries =
            fs::read_dir(directory).map_err(|error| format!("{}: {error}", directory.display()))?;
        for entry in entries {
            let entry = entry.map_err(|error| error.to_string())?;
            let name = entry
                .file_name()
                .into_string()
                .map_err(|name| format!("non-UTF-8 corpus path {name:?}"))?;
            let kind = entry.file_type().map_err(|error| error.to_string())?;
            parts.push(name);
            if kind.is_dir() {
                walk(&entry.path(), parts, out)?;
            } else if parts.last().is_some_and(|name| name.ends_with(".json")) {
                out.push(parts.clone());
            }
            parts.pop();
        }
        Ok(())
    }
    let mut found = Vec::new();
    walk(
        &root.join("corpus"),
        &mut vec!["corpus".to_owned()],
        &mut found,
    )?;
    found.sort();
    Ok(found.into_iter().map(|parts| parts.join("/")).collect())
}

fn read(root: &Path, path: &str) -> Result<Vec<u8>> {
    fs::read(root.join(path)).map_err(|error| format!("{path}: {error}"))
}

fn identity(files: impl IntoIterator<Item = (String, Vec<u8>)>) -> String {
    let mut state = FNV1A64_OFFSET;
    fnv1a64_update(&mut state, BUILDER.as_bytes());
    for (path, bytes) in files {
        fnv1a64_update(&mut state, path.as_bytes());
        fnv1a64_update(&mut state, &bytes);
    }
    format!("{BUILDER}:fnv1a64:{state:016x}")
}

/// The digest the index is bound to: [`BUILDER`] and every indexed path and
/// byte string, length-prefixed, under FNV-1a 64.
pub fn digest(root: &Path) -> Result<String> {
    let paths = inputs(root)?;
    let mut files = Vec::with_capacity(paths.len());
    for path in paths {
        let bytes = read(root, &path)?;
        files.push((path, bytes));
    }
    Ok(identity(files))
}

/// Python `json.dumps(value, ensure_ascii=ascii, sort_keys=True)`.
pub fn dumps(value: &Value, ascii: bool) -> String {
    let mut out = String::new();
    write(value, ascii, &mut out);
    out
}

fn write(value: &Value, ascii: bool, out: &mut String) {
    match value {
        Value::String(text) => out.push_str(&pyfmt::json_str(text, ascii)),
        Value::Number(number) if number.is_f64() => {
            out.push_str(&float_repr(number.as_f64().unwrap_or_default()))
        }
        Value::Array(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                write(item, ascii, out);
            }
            out.push(']');
        }
        Value::Object(map) => {
            out.push('{');
            for (index, (key, item)) in map.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                out.push_str(&pyfmt::json_str(key, ascii));
                out.push_str(": ");
                write(item, ascii, out);
            }
            out.push('}');
        }
        other => out.push_str(&other.to_string()),
    }
}

/// Python `references`: every string value, except under an `id` field.
fn references<'v>(value: &'v Value, out: &mut Vec<&'v str>) {
    match value {
        Value::String(text) => out.push(text),
        Value::Array(items) => items.iter().for_each(|item| references(item, out)),
        Value::Object(map) => map
            .iter()
            .filter(|(field, _)| *field != "id")
            .for_each(|(_, item)| references(item, out)),
        _ => {}
    }
}

/// Python `entities`: the record of a file with a string `id` (its kind is
/// the parent directory name), and each nested passage of a passage
/// collection with its shared snapshot and collection notes.
pub fn entities(path: &str, value: &Value) -> Result<Vec<(String, Obj)>> {
    let mut parts = path.rsplit('/');
    parts.next();
    let kind = parts.next().unwrap_or_default();
    let mut out = Vec::new();
    let Value::Object(object) = value else {
        return Ok(out);
    };
    if object.get("id").is_some_and(Value::is_string) {
        out.push((kind.to_owned(), object.clone()));
    }
    if kind == "passages" {
        let passages = match object.get("passages") {
            None => &[][..],
            Some(Value::Array(items)) => items.as_slice(),
            Some(_) => return Err(format!("invalid nested passage in {path}")),
        };
        for passage in passages {
            let Some(id) = passage
                .as_object()
                .and_then(|passage| passage.get("id"))
                .and_then(Value::as_str)
            else {
                return Err(format!("invalid nested passage in {path}"));
            };
            let mut entity = Obj::new();
            entity.insert("id".into(), json!(id));
            entity.insert("passage".into(), passage.clone());
            entity.insert(
                "snapshot".into(),
                object.get("snapshot").cloned().unwrap_or(Value::Null),
            );
            entity.insert(
                "collection_notes".into(),
                object.get("notes").cloned().unwrap_or(Value::Null),
            );
            out.push(("passages".into(), entity));
        }
    }
    Ok(out)
}

fn parse(path: &str, bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(bytes).map_err(|error| format!("{path}: {error}"))
}

/// Python `build`: projects the corpus into a temporary database next to
/// `destination` and renames it into place, refusing a corpus that changed
/// while it was read and duplicate record identities.
pub fn build(root: &Path, destination: &Path) -> Result<()> {
    let paths = inputs(root)?;
    let mut files = Vec::with_capacity(paths.len());
    for path in paths {
        let bytes = read(root, &path)?;
        files.push((path, bytes));
    }
    let before = identity(
        files
            .iter()
            .map(|(path, bytes)| (path.clone(), bytes.clone())),
    );
    let directory = destination.parent().unwrap_or(Path::new("."));
    fs::create_dir_all(directory).map_err(|error| format!("{}: {error}", directory.display()))?;
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_nanos());
    let temporary = directory.join(format!(
        ".truth-index-{}-{nanos}.sqlite.tmp",
        std::process::id()
    ));
    let outcome = fill(root, &temporary, &files, &before)
        .and_then(|()| fs::rename(&temporary, destination).map_err(|error| error.to_string()));
    let _ = fs::remove_file(&temporary);
    outcome
}

fn fill(root: &Path, temporary: &Path, files: &[(String, Vec<u8>)], before: &str) -> Result<()> {
    let mut db = Connection::open(temporary).map_err(sql)?;
    let tx = db.transaction().map_err(sql)?;
    tx.execute_batch(TABLES).map_err(sql)?;
    let mut records = Vec::new();
    {
        let mut insert = tx
            .prepare("INSERT INTO source_files VALUES (?,?)")
            .map_err(sql)?;
        for (path, bytes) in files {
            insert.execute(params![path, bytes]).map_err(sql)?;
            let value = parse(path, bytes)?;
            for (kind, entity) in entities(path, &value)? {
                records.push((path.as_str(), kind, entity));
            }
        }
    }
    let known: BTreeSet<&str> = records
        .iter()
        .filter_map(|(_, _, record)| record.get("id").and_then(Value::as_str))
        .collect();
    {
        let mut record_row = tx
            .prepare("INSERT INTO records VALUES (?,?,?,?,?)")
            .map_err(sql)?;
        let mut search_row = tx.prepare("INSERT INTO search VALUES (?,?)").map_err(sql)?;
        let mut reference = tx
            .prepare("INSERT OR IGNORE INTO refs VALUES (?,?)")
            .map_err(sql)?;
        let mut argument = tx
            .prepare("INSERT INTO arguments VALUES (?,?,?)")
            .map_err(sql)?;
        for (path, kind, record) in &records {
            let identifier = record.get("id").and_then(Value::as_str).unwrap_or_default();
            let value = Value::Object(record.clone());
            let body = dumps(&value, false);
            let key = format!("{kind}:{identifier}");
            record_row
                .execute(params![key, identifier, kind, path, body])
                .map_err(sql)?;
            search_row.execute(params![key, body]).map_err(sql)?;
            let mut targets = Vec::new();
            references(&value, &mut targets);
            for target in targets.into_iter().filter(|target| known.contains(target)) {
                reference.execute(params![key, target]).map_err(sql)?;
            }
            if kind == "arguments" {
                let premises: BTreeSet<&str> = record
                    .get("premise_statement_ids")
                    .and_then(Value::as_array)
                    .map(|items| items.iter().filter_map(Value::as_str).collect())
                    .unwrap_or_default();
                let signature = dumps(&json!(premises), true);
                let conclusion = record
                    .get("conclusion_statement_id")
                    .and_then(Value::as_str);
                argument
                    .execute(params![identifier, signature, conclusion])
                    .map_err(sql)?;
            }
        }
    }
    if digest(root)? != before {
        return Err("corpus changed while indexing; retry".into());
    }
    tx.execute(
        "INSERT INTO metadata VALUES ('schema',?),('digest',?)",
        params![SCHEMA, before],
    )
    .map_err(sql)?;
    tx.commit().map_err(sql)?;
    db.close().map_err(|(_, error)| sql(error))
}

/// Python `connect`: the index at `path`, read-only, when it is bound to
/// the current corpus; otherwise an error.
pub fn connect(root: &Path, path: &Path) -> Result<Connection> {
    let db = Connection::open_with_flags(path, OpenFlags::SQLITE_OPEN_READ_ONLY).map_err(sql)?;
    let metadata: BTreeMap<String, String> = {
        let mut statement = db.prepare("SELECT key,value FROM metadata").map_err(sql)?;
        statement
            .query_map([], |row| Ok((row.get(0)?, row.get(1)?)))
            .map_err(sql)?
            .collect::<std::result::Result<_, _>>()
            .map_err(sql)?
    };
    if metadata.get("schema").map(String::as_str) != Some(SCHEMA)
        || metadata.get("digest") != Some(&digest(root)?)
    {
        return Err("index is stale; run build again".into());
    }
    Ok(db)
}

/// The fresh index of `root` (Python `cached_related`'s refresh): reused
/// when it is bound to the current corpus, otherwise rebuilt first. Returns
/// whether it was rebuilt.
pub fn open(root: &Path) -> Result<(Connection, bool)> {
    let path = database(root);
    if path.exists()
        && let Ok(db) = connect(root, &path)
    {
        return Ok((db, false));
    }
    build(root, &path)?;
    Ok((connect(root, &path)?, true))
}

fn rows(db: &Connection, query: &str, values: &[&dyn rusqlite::ToSql]) -> Result<Vec<Value>> {
    let mut statement = db.prepare(query).map_err(sql)?;
    let names: Vec<String> = statement.column_names().map(str::to_owned).collect();
    let found = statement
        .query_map(values, |row| {
            let mut object = Obj::new();
            for (index, name) in names.iter().enumerate() {
                let value: Option<String> = row.get(index)?;
                object.insert(name.clone(), value.map_or(Value::Null, Value::String));
            }
            Ok(Value::Object(object))
        })
        .map_err(sql)?
        .collect::<std::result::Result<Vec<_>, _>>()
        .map_err(sql)?;
    Ok(found)
}

fn body(text: &str) -> Result<Obj> {
    serde_json::from_str(text).map_err(|error| error.to_string())
}

/// Every record of the index as `(kind, body)`, for alias resolution.
fn aliases(db: &Connection) -> Result<Aliases> {
    let mut aliases = Aliases::default();
    let mut statement = db
        .prepare("SELECT kind,body FROM records ORDER BY rowid")
        .map_err(sql)?;
    let mut found = statement.query([]).map_err(sql)?;
    while let Some(row) = found.next().map_err(sql)? {
        let kind: String = row.get(0).map_err(sql)?;
        let text: String = row.get(1).map_err(sql)?;
        aliases.add(&kind, &body(&text)?);
    }
    Ok(aliases)
}

/// The key (`kind:ID`) a token names: an indexed ID or key as Python looks
/// it up, else (an extension) a legacy id or label, optionally `kind:`-prefixed.
fn key_of(db: &Connection, token: &str) -> Result<String> {
    let keys: Vec<String> = {
        let mut statement = db
            .prepare("SELECT key FROM records WHERE id=?1 OR key=?1")
            .map_err(sql)?;
        statement
            .query_map([token], |row| row.get(0))
            .map_err(sql)?
            .collect::<std::result::Result<_, _>>()
            .map_err(sql)?
    };
    match keys.as_slice() {
        [key] => return Ok(key.clone()),
        [_, _, ..] => {
            return Err(format!(
                "ambiguous ID; use kind:ID, for example results:{token}"
            ));
        }
        [] => {}
    }
    let aliases = aliases(db)?;
    let kinds: BTreeSet<String> = {
        let mut statement = db
            .prepare("SELECT DISTINCT kind FROM records")
            .map_err(sql)?;
        statement
            .query_map([], |row| row.get(0))
            .map_err(sql)?
            .collect::<std::result::Result<_, _>>()
            .map_err(sql)?
    };
    // A `kind:` prefix counts only when it names an indexed kind and the
    // rest names a record of it; otherwise the whole token (a label may
    // contain a colon) is looked up.
    let scoped = token
        .split_once(':')
        .filter(|(kind, _)| kinds.contains(*kind))
        .map(|(kind, name)| aliases.candidates(name, Some(&[kind])))
        .filter(|found| !found.is_empty());
    let candidates = scoped.unwrap_or_else(|| aliases.candidates(token, None));
    match candidates.as_slice() {
        [] => Err(format!("unknown record: {token}")),
        [(kind, id)] => Ok(format!("{kind}:{id}")),
        many => Err(format!(
            "{token:?} names several records: {}; use kind:ID",
            aliases.describe(many)
        )),
    }
}

/// Python `record`: the record a token names.
pub fn record(db: &Connection, token: &str) -> Result<Obj> {
    let key = key_of(db, token)?;
    let text: String = db
        .query_row("SELECT body FROM records WHERE key=?", [&key], |row| {
            row.get(0)
        })
        .map_err(sql)?;
    body(&text)
}

/// Python `lookup` (`show`): the record and the records that reference it.
pub fn show(db: &Connection, token: &str) -> Result<Value> {
    let found = record(db, token)?;
    let id = found
        .get("id")
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_owned();
    let referenced_by = rows(
        db,
        "SELECT r.id,r.kind,r.path FROM refs JOIN records r ON r.key=refs.owner WHERE target=? ORDER BY r.kind,r.id",
        &[&id],
    )?;
    Ok(json!({"record": found, "referenced_by": referenced_by}))
}

/// Python `search`: literal words, all of which must match, by FTS5 rank.
pub fn search(db: &Connection, query: &str, limit: i64) -> Result<Value> {
    let words: Vec<&str> = query
        .split(pyfmt::is_space)
        .filter(|word| !word.is_empty())
        .collect();
    if words.is_empty() {
        return Err("search requires at least one word".into());
    }
    let expression = words
        .iter()
        .map(|word| format!("\"{}\"", word.replace('"', "\"\"")))
        .collect::<Vec<_>>()
        .join(" AND ");
    let limit = limit.clamp(1, 200);
    Ok(Value::Array(rows(
        db,
        "SELECT r.id,r.kind,r.path FROM search JOIN records r ON r.key=search.id WHERE search MATCH ? ORDER BY rank LIMIT ?",
        &[&expression as &dyn rusqlite::ToSql, &limit],
    )?))
}

/// Python `duplicates`: arguments with the same premise-ID set and
/// conclusion ID. Exact matches only; no equivalence or redundancy claim.
pub fn duplicates(db: &Connection) -> Result<Vec<Value>> {
    let groups: Vec<(String, Option<String>)> = {
        let mut statement = db
            .prepare("SELECT signature,conclusion FROM arguments GROUP BY signature,conclusion HAVING count(*)>1")
            .map_err(sql)?;
        statement
            .query_map([], |row| Ok((row.get(0)?, row.get(1)?)))
            .map_err(sql)?
            .collect::<std::result::Result<_, _>>()
            .map_err(sql)?
    };
    let mut statement = db
        .prepare("SELECT id FROM arguments WHERE signature=? AND conclusion=? ORDER BY id")
        .map_err(sql)?;
    let mut out = Vec::new();
    for (signature, conclusion) in groups {
        let ids: Vec<String> = statement
            .query_map(params![signature, conclusion], |row| row.get(0))
            .map_err(sql)?
            .collect::<std::result::Result<_, _>>()
            .map_err(sql)?;
        let premises: Value =
            serde_json::from_str(&signature).map_err(|error| error.to_string())?;
        out.push(
            json!({"premise_statement_ids": premises, "conclusion_statement_id": conclusion,
                        "argument_ids": ids}),
        );
    }
    Ok(out)
}

/// Python `summary`: the registered inventory.
pub fn summary(db: &Connection) -> Result<Value> {
    let mut counts = Obj::new();
    let mut statement = db
        .prepare("SELECT kind,count(*) FROM records GROUP BY kind")
        .map_err(sql)?;
    let mut found = statement.query([]).map_err(sql)?;
    while let Some(row) = found.next().map_err(sql)? {
        let kind: String = row.get(0).map_err(sql)?;
        let count: i64 = row.get(1).map_err(sql)?;
        counts.insert(kind, json!(count));
    }
    Ok(
        json!({"mode": "registered inventory, not certified progress",
              "records_by_kind": counts,
              "exact_duplicate_argument_groups": duplicates(db)?.len()}),
    )
}

/// Python `parity`: every corpus file's bytes and every projected record,
/// recomputed from the files, against the index.
pub fn parity(db: &Connection, root: &Path) -> Result<Value> {
    let mut indexed_files: BTreeMap<String, Vec<u8>> = BTreeMap::new();
    {
        let mut statement = db
            .prepare("SELECT path,content FROM source_files")
            .map_err(sql)?;
        let mut found = statement.query([]).map_err(sql)?;
        while let Some(row) = found.next().map_err(sql)? {
            indexed_files.insert(row.get(0).map_err(sql)?, row.get(1).map_err(sql)?);
        }
    }
    let mut current = BTreeMap::new();
    for path in inputs(root)? {
        let bytes = read(root, &path)?;
        current.insert(path, bytes);
    }
    let mut issues = Vec::new();
    let paths: BTreeSet<&String> = indexed_files.keys().chain(current.keys()).collect();
    for path in paths {
        if indexed_files.get(path) != current.get(path) {
            issues.push(json!({"path": path, "issue": "missing or unequal source bytes"}));
        }
    }
    let mut expected = BTreeMap::new();
    let mut nonrecords = Vec::new();
    for (path, bytes) in &current {
        let projected = entities(path, &parse(path, bytes)?)?;
        if projected.is_empty() {
            nonrecords.push(path.clone());
        }
        for (kind, entity) in projected {
            let id = entity.get("id").and_then(Value::as_str).unwrap_or_default();
            expected.insert(format!("{kind}:{id}"), Value::Object(entity.clone()));
        }
    }
    let mut indexed = BTreeMap::new();
    {
        let mut statement = db.prepare("SELECT key,body FROM records").map_err(sql)?;
        let mut found = statement.query([]).map_err(sql)?;
        while let Some(row) = found.next().map_err(sql)? {
            let key: String = row.get(0).map_err(sql)?;
            let text: String = row.get(1).map_err(sql)?;
            let value: Value = serde_json::from_str(&text).unwrap_or(Value::Null);
            indexed.insert(key, value);
        }
    }
    let keys: BTreeSet<&String> = expected.keys().chain(indexed.keys()).collect();
    for key in keys {
        if expected.get(key) != indexed.get(key) {
            issues.push(json!({"path": key, "issue": "missing or unequal query record"}));
        }
    }
    Ok(json!({
        "status": if issues.is_empty() { "equal" } else { "mismatch" },
        "source_files": current.len(),
        "queryable_records": expected.len(),
        "preserved_nonrecord_files": nonrecords,
        "issues": issues,
        "scope": "Storage and record parity only; not proof verification or complete CLI feature parity.",
    }))
}

/// Python `export`: the original bytes of one indexed corpus file.
pub fn export(db: &Connection, path: &str) -> Result<Vec<u8>> {
    db.query_row(
        "SELECT content FROM source_files WHERE path=?",
        [path],
        |row| row.get(0),
    )
    .optional()
    .map_err(sql)?
    .ok_or_else(|| format!("unknown indexed path: {path}"))
}

/// The records of the kinds a configuration query reads, by ID.
pub struct Tables {
    records: BTreeMap<&'static str, Vec<Obj>>,
}

impl Tables {
    pub fn load(db: &Connection) -> Result<Self> {
        let mut records = BTreeMap::new();
        for kind in ["results", "arguments", "models"] {
            let mut statement = db
                .prepare("SELECT body FROM records WHERE kind=? ORDER BY rowid")
                .map_err(sql)?;
            let bodies: Vec<String> = statement
                .query_map([kind], |row| row.get(0))
                .map_err(sql)?
                .collect::<std::result::Result<_, _>>()
                .map_err(sql)?;
            records.insert(
                kind,
                bodies
                    .iter()
                    .map(|text| body(text))
                    .collect::<Result<Vec<_>>>()?,
            );
        }
        Ok(Self { records })
    }

    pub fn index(&self, kind: &str) -> Index<'_> {
        self.records
            .get(kind)
            .into_iter()
            .flatten()
            .map(|record| (configurations::str_of(record, "id"), record))
            .collect()
    }
}

/// The configuration case a token names (`bundle requires a configuration
/// case ID` otherwise).
pub fn case(db: &Connection, token: &str) -> Result<Obj> {
    let case = record(db, token)?;
    if !case.contains_key("semantics") || !case.contains_key("configurations") {
        return Err("bundle requires a configuration case ID".into());
    }
    Ok(case)
}

/// Resolves statement tokens: an indexed statement ID as given, else a
/// legacy id or label of one statement; anything else stays as given.
pub fn statements(db: &Connection, tokens: &[String]) -> Result<Vec<String>> {
    let mut aliases = None;
    let mut out = Vec::new();
    for token in tokens {
        let token = &token
            .strip_prefix("statements:")
            .map_or_else(|| token.clone(), str::to_owned);
        let exact: Option<String> = db
            .query_row(
                "SELECT id FROM records WHERE key=?",
                [format!("statements:{token}")],
                |row| row.get(0),
            )
            .optional()
            .map_err(sql)?;
        if exact.is_some() {
            out.push(token.clone());
            continue;
        }
        if aliases.is_none() {
            aliases = Some(self::aliases(db)?);
        }
        let aliases = aliases.as_ref().expect("built");
        out.push(match aliases.resolve(token, Some(&["statements"])) {
            Ok(id) => id,
            Err(Unresolved::Unknown) => token.clone(),
            Err(Unresolved::Ambiguous(candidates)) => {
                return Err(format!(
                    "{token:?} names several records: {}; pass a uuid",
                    aliases.describe(&candidates)
                ));
            }
        });
    }
    Ok(out)
}

/// Python `bundle`: the registered-only configuration report of one case
/// for a premise selection, with the registered implications whose premises
/// it contains. Not verification evidence.
pub fn bundle(case: &Obj, tables: &Tables, premises: &[String]) -> Result<Value> {
    let applications = case
        .get("semantics")
        .and_then(|semantics| semantics.get("applications"))
        .and_then(Value::as_object)
        .ok_or("configuration case without semantics.applications")?;
    let unknown: BTreeSet<&str> = premises
        .iter()
        .map(String::as_str)
        .filter(|premise| !applications.contains_key(*premise))
        .collect();
    if !unknown.is_empty() {
        return Err(format!(
            "statements outside selected profile: {}",
            unknown.into_iter().collect::<Vec<_>>().join(", ")
        ));
    }
    let (results, arguments, models) = (
        tables.index("results"),
        tables.index("arguments"),
        tables.index("models"),
    );
    let selected: BTreeSet<&str> = premises.iter().map(String::as_str).collect();
    let report = configurations::configuration_report(
        case,
        &results,
        &arguments,
        &models,
        false,
        Some(("query", selected.iter().copied().collect())),
    )?;
    let mut rules = Vec::new();
    for rid in configurations::strs(case, "implication_result_ids") {
        let result = results
            .get(rid)
            .ok_or_else(|| format!("unknown implication result {rid}"))?;
        let argument = arguments
            .get(configurations::str_of(result, "argument_id"))
            .ok_or_else(|| format!("unknown argument of result {rid}"))?;
        let needed = configurations::strs(argument, "premise_statement_ids");
        if needed.iter().all(|premise| selected.contains(premise)) {
            rules.push(json!({"result_id": rid, "theorem": result.get("theorem"),
                              "premise_statement_ids": argument.get("premise_statement_ids"),
                              "conclusion_statement_id": argument.get("conclusion_statement_id")}));
        }
    }
    Ok(json!({"mode": "registered-only",
              "certification": "Not verification evidence. Use existing configuration verification commands.",
              "applicable_registered_implications": rules, "report": report}))
}

/// Python `compare`: registered implication supports from each side to the
/// other, within one case. Candidate paths only: a missing path is not
/// non-entailment or strict strength.
pub fn compare(
    case_id: &str,
    case: &Obj,
    tables: &Tables,
    left: &[String],
    right: &[String],
) -> Result<Value> {
    bundle(case, tables, left)?;
    bundle(case, tables, right)?;
    let (results, arguments) = (tables.index("results"), tables.index("arguments"));
    let rules = configurations::strs(case, "implication_result_ids");
    for rid in &rules {
        let result = results
            .get(rid)
            .ok_or_else(|| format!("unknown implication result {rid}"))?;
        if !arguments.contains_key(configurations::str_of(result, "argument_id")) {
            return Err(format!("unknown argument of result {rid}"));
        }
    }
    let direction = |source: &[String], target: &[String]| {
        let assumptions: BTreeSet<&str> = source.iter().map(String::as_str).collect();
        let closure = configurations::implication_closure(
            &assumptions,
            &rules,
            &results,
            &arguments,
            128,
            true,
        );
        let mut closure = closure.to_json(&results);
        let mut found = BTreeSet::new();
        for item in closure["items"].as_array_mut().into_iter().flatten() {
            item["minimality"] =
                json!("minimal supports from registered rules only; verification required");
            if let Some(id) = item["statement_id"].as_str() {
                found.insert(id.to_owned());
            }
        }
        let missing: BTreeSet<&str> = target
            .iter()
            .map(String::as_str)
            .filter(|id| !found.contains(*id))
            .collect();
        json!({"registered_paths_cover_target": missing.is_empty(),
               "missing_statement_ids": missing, "closure": closure})
    };
    Ok(
        json!({"mode": "registered-only candidate comparison", "case_id": case_id,
              "warning": "Paths require verification. Missing paths do not prove non-entailment or strict strength.",
              "left_to_right": direction(left, right), "right_to_left": direction(right, left)}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Fixture(PathBuf);

    impl Fixture {
        fn new(name: &str) -> Self {
            let root = std::env::temp_dir().join(format!(
                "truth-index-{name}-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map_or(0, |elapsed| elapsed.as_nanos())
            ));
            let fixture = Self(root);
            fixture.put(
                "statements",
                json!({"id": "S", "paraphrase": "a statement"}),
            );
            fixture.put(
                "arguments",
                json!({"id": "A", "premise_statement_ids": ["S"], "conclusion_statement_id": "T"}),
            );
            fixture.put(
                "arguments",
                json!({"id": "B", "premise_statement_ids": ["S"], "conclusion_statement_id": "T"}),
            );
            fixture.put("results", json!({"id": "A", "argument_id": "A"}));
            fixture
        }

        fn put(&self, kind: &str, value: Value) {
            let directory = self.0.join("corpus").join(kind);
            fs::create_dir_all(&directory).unwrap();
            let id = value["id"].as_str().unwrap().to_owned();
            fs::write(directory.join(format!("{id}.json")), value.to_string()).unwrap();
        }

        fn open(&self) -> Connection {
            open(&self.0).unwrap().0
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn fts5_is_compiled_in() {
        let db = Connection::open_in_memory().unwrap();
        db.execute_batch("CREATE VIRTUAL TABLE t USING fts5(x)")
            .unwrap();
    }

    #[test]
    fn python_dumps() {
        let value: Value =
            serde_json::from_str(r#"{"b": [1, 2.5, 91.0, "é\n"], "a": null, "c": {"z": true}}"#)
                .unwrap();
        assert_eq!(
            dumps(&value, false),
            r#"{"a": null, "b": [1, 2.5, 91.0, "é\n"], "c": {"z": true}}"#
        );
        assert_eq!(dumps(&json!(["\u{e9}"]), true), "[\"\\u00e9\"]");
    }

    #[test]
    fn namespaced_identity_reverse_links_and_duplicates() {
        let fixture = Fixture::new("identity");
        let db = fixture.open();
        assert!(record(&db, "A").unwrap_err().contains("ambiguous"));
        assert_eq!(record(&db, "results:A").unwrap()["argument_id"], "A");
        let referenced = show(&db, "S").unwrap();
        let ids: BTreeSet<&str> = referenced["referenced_by"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["id"].as_str().unwrap())
            .collect();
        assert_eq!(ids, BTreeSet::from(["A", "B"]));
        assert_eq!(
            duplicates(&db).unwrap()[0]["argument_ids"],
            json!(["A", "B"])
        );
        let by_argument = show(&db, "arguments:A").unwrap();
        assert_eq!(
            by_argument["referenced_by"],
            json!([{"id": "A", "kind": "results", "path": "corpus/results/A.json"}])
        );
        assert_eq!(
            show(&db, "arguments:B").unwrap()["referenced_by"],
            json!([])
        );
        assert!(
            record(&db, "MISSING")
                .unwrap_err()
                .contains("unknown record")
        );
    }

    #[test]
    fn stale_index_is_rejected_and_refreshed() {
        let fixture = Fixture::new("stale");
        drop(fixture.open());
        fixture.put(
            "statements",
            json!({"id": "S", "paraphrase": "changed words"}),
        );
        let path = database(&fixture.0);
        assert!(connect(&fixture.0, &path).unwrap_err().contains("stale"));
        let (db, rebuilt) = open(&fixture.0).unwrap();
        assert!(rebuilt);
        assert_eq!(
            search(&db, "changed", 20).unwrap(),
            json!([{"id": "S", "kind": "statements", "path": "corpus/statements/S.json"}])
        );
        drop(db);
        assert!(!open(&fixture.0).unwrap().1);
    }

    #[test]
    fn failed_rebuild_preserves_previous_database() {
        let fixture = Fixture::new("failed");
        drop(fixture.open());
        let path = database(&fixture.0);
        let previous = fs::read(&path).unwrap();
        fs::write(fixture.0.join("corpus/statements/broken.json"), "{broken").unwrap();
        assert!(build(&fixture.0, &path).is_err());
        assert_eq!(fs::read(&path).unwrap(), previous);
        assert_eq!(
            fs::read_dir(path.parent().unwrap()).unwrap().count(),
            1,
            "no temporary file is left behind"
        );
    }

    #[test]
    fn nested_passages_and_nonrecord_files_keep_parity() {
        let fixture = Fixture::new("passages");
        let directory = fixture.0.join("corpus/passages");
        fs::create_dir_all(&directory).unwrap();
        fs::write(
            directory.join("collection.json"),
            json!({"snapshot": {"source_id": "SOURCE", "revision": "pinned"},
                   "passages": [{"id": "PASSAGE-1", "locator": "chapter 1"},
                                {"id": "PASSAGE-2", "locator": "chapter 2"}]})
            .to_string(),
        )
        .unwrap();
        let raw = b"{ \"title\": \"schema without an entity ID\" }\n";
        fs::write(fixture.0.join("corpus/schema.json"), raw).unwrap();
        let db = fixture.open();
        let passage = record(&db, "PASSAGE-1").unwrap();
        assert_eq!(passage["snapshot"]["revision"], "pinned");
        assert_eq!(passage["passage"]["locator"], "chapter 1");
        assert_eq!(passage["collection_notes"], Value::Null);
        let report = parity(&db, &fixture.0).unwrap();
        assert_eq!(report["status"], "equal");
        assert_eq!(
            report["preserved_nonrecord_files"],
            json!(["corpus/schema.json"])
        );
        assert_eq!(export(&db, "corpus/schema.json").unwrap(), raw);
        assert_eq!(
            search(&db, "chapter", 20)
                .unwrap()
                .as_array()
                .unwrap()
                .len(),
            2
        );
    }

    #[test]
    fn parity_detects_a_corrupt_projection() {
        let fixture = Fixture::new("corrupt");
        drop(fixture.open());
        let path = database(&fixture.0);
        let writer = Connection::open(&path).unwrap();
        writer
            .execute("UPDATE records SET body='{}' WHERE id='S'", [])
            .unwrap();
        drop(writer);
        let db = connect(&fixture.0, &path).unwrap();
        assert_eq!(parity(&db, &fixture.0).unwrap()["status"], "mismatch");
    }

    #[test]
    fn profile_boundary_and_uncertified_status() {
        let fixture = Fixture::new("profile");
        fixture.put(
            "configurations",
            json!({"id": "CONFIG-X", "seed_statement_id": "S",
                   "semantics": {"applications": {"S": []}}, "configurations": []}),
        );
        let db = fixture.open();
        let case = case(&db, "CONFIG-X").unwrap();
        let tables = Tables::load(&db).unwrap();
        assert!(
            bundle(&case, &tables, &["T".into()])
                .unwrap_err()
                .contains("outside selected profile")
        );
        let output = bundle(&case, &tables, &["S".into()]).unwrap();
        assert_eq!(output["report"]["verified"], false);
        let comparison = compare("CONFIG-X", &case, &tables, &["S".into()], &["S".into()]).unwrap();
        assert_eq!(
            comparison["left_to_right"]["registered_paths_cover_target"],
            true
        );
        assert!(
            comparison["left_to_right"]["closure"]["items"][0]["minimality"]
                .as_str()
                .unwrap()
                .contains("verification required")
        );
    }

    #[test]
    fn labels_with_colons_and_kind_prefixes_resolve() {
        let fixture = Fixture::new("labels");
        fixture.put(
            "configurations",
            json!({"id": "CONFIG-X", "label": "First slice: a case",
                   "semantics": {"applications": {"S": []}}, "configurations": []}),
        );
        fixture.put(
            "statements",
            json!({"id": "U", "legacy_id": "STMT-U", "label": "U: a premise"}),
        );
        let db = fixture.open();
        assert_eq!(
            record(&db, "First slice: a case").unwrap()["id"],
            "CONFIG-X"
        );
        assert_eq!(
            record(&db, "configurations:First slice: a case").unwrap()["id"],
            "CONFIG-X"
        );
        assert_eq!(record(&db, "statements:STMT-U").unwrap()["id"], "U");
        assert_eq!(
            statements(
                &db,
                &[
                    "statements:S".into(),
                    "statements:STMT-U".into(),
                    "U: a premise".into()
                ]
            )
            .unwrap(),
            vec!["S", "U", "U"]
        );
    }

    #[test]
    fn inputs_follow_python_path_order() {
        let fixture = Fixture::new("order");
        for directory in ["a-b", "a"] {
            fs::create_dir_all(fixture.0.join("corpus").join(directory)).unwrap();
            fs::write(
                fixture.0.join("corpus").join(directory).join("x.json"),
                "{}",
            )
            .unwrap();
        }
        fs::write(fixture.0.join("corpus/a.b.json"), "{}").unwrap();
        let paths = inputs(&fixture.0).unwrap();
        let position = |path: &str| paths.iter().position(|item| item == path).unwrap();
        assert!(position("corpus/a/x.json") < position("corpus/a-b/x.json"));
        assert!(position("corpus/a-b/x.json") < position("corpus/a.b.json"));
    }
}
