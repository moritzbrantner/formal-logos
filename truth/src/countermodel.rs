//! Finite omission countermodels for a Lean theorem (`truth countermodel`,
//! docs/countermodels.md).
//!
//! For `thm (Carriers) (Predicates) (h₁ : P₁) … (hₙ : Pₙ) : C`, the omission
//! model for premise k interprets the carriers as `Fin m` and the predicates
//! and unary carrier functions as finite tables so that every Pᵢ with i ≠ k
//! holds and C fails. The search
//! grounds the first-order skeleton that `scripts/Countermodel.lean` extracts,
//! encodes it in CNF and runs a small DPLL solver that prefers false atoms. A
//! found model is only a candidate: it is rendered as Lean `abbrev`s with a
//! `delta …; decide` certificate, which Lean checks unless the caller skips
//! it. "No model within bounds" is reported as unresolved; it never shows that
//! the premise is needed.
//!
//! For function-free skeletons, the search order (carrier sizes, constants,
//! atom numbering, false-first branching) is the one the retired
//! `scripts/countermodel.py` used, so the same theorem yields the same models.
//! Function tables are enumerated lazily inside each constant assignment.

use crate::{
    structure::{self, Sources, os_error},
    subprocess::Finished,
};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fs,
    path::Path,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

/// The extractor, relative to the repository root.
pub const EXTRACTOR: &str = "scripts/Countermodel.lean";
const BUILD_TIMEOUT: Duration = Duration::from_secs(3600);
const EXTRACT_TIMEOUT: Duration = Duration::from_secs(300);
const CHECK_TIMEOUT: Duration = Duration::from_secs(600);

// --- skeleton ----------------------------------------------------------------

/// An argument sort of a predicate: a carrier, or a carrier predicate
/// `T₁ → … → Tₙ → Prop` (a set of points).
#[derive(Clone, Debug, PartialEq)]
pub enum Sort {
    Carrier(String),
    Set(Vec<String>),
}

/// A term: a variable or constant, a unary carrier-function application, or a
/// predicate-valued `fun xs => body`.
#[derive(Clone, Debug)]
pub enum Term {
    Var(String),
    App(String, Box<Term>),
    Lam(Vec<(String, String)>, Box<Formula>),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Connective {
    And,
    Or,
    Imp,
    Iff,
}

/// A formula of the extracted fragment.
#[derive(Clone, Debug)]
pub enum Formula {
    True,
    False,
    Not(Box<Formula>),
    Binary(Connective, Box<Formula>, Box<Formula>),
    /// `∀`/`∃`; `sort` `None` ranges over `Prop` (the two truth values).
    Quantifier {
        exists: bool,
        var: String,
        sort: Option<String>,
        body: Box<Formula>,
    },
    Eq(Term, Term),
    Atom(String, Vec<Term>),
}

pub struct Premise {
    pub name: String,
    pub lean: String,
    pub formula: Formula,
}

/// A total, nondependent unary function between two declared carriers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnaryFunction {
    pub name: String,
    pub domain: String,
    pub codomain: String,
}

/// The first-order skeleton of a theorem, as `scripts/Countermodel.lean`
/// writes it (plus the module it was read from).
pub struct Skeleton {
    pub theorem: String,
    pub carriers: Vec<String>,
    pub predicates: Vec<(String, Vec<Sort>)>,
    pub constants: Vec<(String, String)>,
    pub functions: Vec<UnaryFunction>,
    pub premises: Vec<Premise>,
    pub conclusion_lean: String,
    pub conclusion: Formula,
    pub unfolded: Vec<String>,
    pub module: String,
}

fn field<'v>(value: &'v Value, key: &str) -> Result<&'v Value, String> {
    value
        .get(key)
        .ok_or_else(|| format!("skeleton node without {key:?}: {value}"))
}

fn text(value: &Value, key: &str) -> Result<String, String> {
    field(value, key)?
        .as_str()
        .map(str::to_owned)
        .ok_or_else(|| format!("skeleton field {key:?} is not a string: {value}"))
}

fn list<'v>(value: &'v Value, key: &str) -> Result<&'v Vec<Value>, String> {
    field(value, key)?
        .as_array()
        .ok_or_else(|| format!("skeleton field {key:?} is not a list: {value}"))
}

fn strings(value: &Value, key: &str) -> Result<Vec<String>, String> {
    list(value, key)?
        .iter()
        .map(|item| {
            item.as_str()
                .map(str::to_owned)
                .ok_or_else(|| format!("skeleton field {key:?} holds a non-string: {item}"))
        })
        .collect()
}

fn parse_sort(value: &Value) -> Result<Sort, String> {
    match value {
        Value::String(carrier) => Ok(Sort::Carrier(carrier.clone())),
        _ => Ok(Sort::Set(strings(value, "set")?)),
    }
}

fn parse_term(value: &Value) -> Result<Term, String> {
    if let Some(name) = value.get("v") {
        return Ok(Term::Var(
            name.as_str()
                .ok_or_else(|| format!("variable name is not a string: {value}"))?
                .to_owned(),
        ));
    }
    if value.get("app").is_some() {
        return Ok(Term::App(
            text(value, "app")?,
            Box::new(parse_term(field(value, "arg")?)?),
        ));
    }
    let vars = list(value, "lam")?
        .iter()
        .map(|var| Ok((text(var, "v")?, text(var, "sort")?)))
        .collect::<Result<_, String>>()?;
    Ok(Term::Lam(
        vars,
        Box::new(parse_formula(field(value, "body")?)?),
    ))
}

/// One formula node of the extractor's JSON.
pub fn parse_formula(value: &Value) -> Result<Formula, String> {
    let sub = |key| parse_formula(field(value, key)?).map(Box::new);
    let binary = |connective| Ok(Formula::Binary(connective, sub("a")?, sub("b")?));
    match text(value, "t")?.as_str() {
        "true" => Ok(Formula::True),
        "false" => Ok(Formula::False),
        "not" => Ok(Formula::Not(sub("a")?)),
        "and" => binary(Connective::And),
        "or" => binary(Connective::Or),
        "imp" => binary(Connective::Imp),
        "iff" => binary(Connective::Iff),
        kind @ ("forall" | "exists") => {
            let sort = text(value, "sort")?;
            Ok(Formula::Quantifier {
                exists: kind == "exists",
                var: text(value, "v")?,
                sort: (sort != "Prop").then_some(sort),
                body: sub("body")?,
            })
        }
        "eq" => Ok(Formula::Eq(
            parse_term(field(value, "a")?)?,
            parse_term(field(value, "b")?)?,
        )),
        "atom" => Ok(Formula::Atom(
            text(value, "p")?,
            list(value, "args")?
                .iter()
                .map(parse_term)
                .collect::<Result<_, _>>()?,
        )),
        other => Err(format!("unknown formula node {other}")),
    }
}

impl Skeleton {
    /// The extractor's output; an `error` object is the extractor's refusal.
    pub fn parse(value: &Value, module: &str) -> Result<Self, String> {
        if let Some(error) = value.get("error") {
            let theorem = value.get("theorem").and_then(Value::as_str);
            let message = error
                .as_str()
                .map_or_else(|| error.to_string(), str::to_owned);
            return Err(match theorem {
                Some(theorem) => format!("{theorem}: {message}"),
                None => message,
            });
        }
        let conclusion = field(value, "conclusion")?;
        let functions = match value.get("functions") {
            None => Vec::new(),
            Some(_) => list(value, "functions")?
                .iter()
                .map(|f| {
                    Ok(UnaryFunction {
                        name: text(f, "name")?,
                        domain: text(f, "domain")?,
                        codomain: text(f, "codomain")?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?,
        };
        let skeleton = Skeleton {
            theorem: text(value, "theorem")?,
            carriers: strings(value, "carriers")?,
            predicates: list(value, "predicates")?
                .iter()
                .map(|p| {
                    Ok((
                        text(p, "name")?,
                        list(p, "args")?
                            .iter()
                            .map(parse_sort)
                            .collect::<Result<_, String>>()?,
                    ))
                })
                .collect::<Result<_, String>>()?,
            constants: list(value, "constants")?
                .iter()
                .map(|c| Ok((text(c, "name")?, text(c, "sort")?)))
                .collect::<Result<_, String>>()?,
            functions,
            premises: list(value, "premises")?
                .iter()
                .map(|p| {
                    Ok(Premise {
                        name: text(p, "name")?,
                        lean: text(p, "lean")?,
                        formula: parse_formula(field(p, "formula")?)?,
                    })
                })
                .collect::<Result<_, String>>()?,
            conclusion_lean: text(conclusion, "lean")?,
            conclusion: parse_formula(field(conclusion, "formula")?)?,
            unfolded: strings(value, "unfolded")?,
            module: module.to_owned(),
        };
        skeleton.validate_function_signatures()?;
        Ok(skeleton)
    }

    fn validate_function_signatures(&self) -> Result<(), String> {
        let carriers: BTreeSet<&str> = self.carriers.iter().map(String::as_str).collect();
        if !self.functions.is_empty() && carriers.len() != self.carriers.len() {
            return Err("duplicate carrier names in function signatures".into());
        }
        let mut names: BTreeSet<&str> = carriers
            .iter()
            .copied()
            .chain(self.predicates.iter().map(|(name, _)| name.as_str()))
            .chain(self.constants.iter().map(|(name, _)| name.as_str()))
            .collect();
        for function in &self.functions {
            if function.name.is_empty() || !names.insert(function.name.as_str()) {
                return Err(format!(
                    "duplicate or empty function name {:?}",
                    function.name
                ));
            }
            for (role, carrier) in [
                ("domain", &function.domain),
                ("codomain", &function.codomain),
            ] {
                if !carriers.contains(carrier.as_str()) {
                    return Err(format!(
                        "function {} has unknown {role} carrier {carrier}",
                        function.name
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn premise_names(&self) -> Vec<&str> {
        self.premises.iter().map(|p| p.name.as_str()).collect()
    }

    /// Whether any formula quantifies over `Prop` (closed by `Classical.em`).
    fn quantifies_over_prop(&self) -> bool {
        fn formula(f: &Formula) -> bool {
            match f {
                Formula::True | Formula::False => false,
                Formula::Not(a) => formula(a),
                Formula::Binary(_, a, b) => formula(a) || formula(b),
                Formula::Quantifier { sort, body, .. } => sort.is_none() || formula(body),
                Formula::Eq(a, b) => term(a) || term(b),
                Formula::Atom(_, args) => args.iter().any(term),
            }
        }
        fn term(t: &Term) -> bool {
            match t {
                Term::Var(_) => false,
                Term::App(_, argument) => term(argument),
                Term::Lam(_, body) => formula(body),
            }
        }
        self.premises.iter().any(|p| formula(&p.formula)) || formula(&self.conclusion)
    }
}

// --- propositional layer ---------------------------------------------------

/// A ground propositional formula; `Const` folds away as it is built.
#[derive(Clone, Debug)]
enum Prop {
    Const(bool),
    Var(usize),
    Not(Box<Prop>),
    And(Vec<Prop>),
    Or(Vec<Prop>),
}

fn neg(f: Prop) -> Prop {
    match f {
        Prop::Const(value) => Prop::Const(!value),
        Prop::Not(inner) => *inner,
        f => Prop::Not(Box::new(f)),
    }
}

fn conj(fs: Vec<Prop>) -> Prop {
    let mut out = Vec::new();
    for f in fs {
        match f {
            Prop::Const(false) => return Prop::Const(false),
            Prop::Const(true) => {}
            Prop::And(parts) => out.extend(parts),
            f => out.push(f),
        }
    }
    match out.len() {
        0 => Prop::Const(true),
        1 => out.pop().expect("one part"),
        _ => Prop::And(out),
    }
}

fn disj(fs: Vec<Prop>) -> Prop {
    let mut out = Vec::new();
    for f in fs {
        match f {
            Prop::Const(true) => return Prop::Const(true),
            Prop::Const(false) => {}
            Prop::Or(parts) => out.extend(parts),
            f => out.push(f),
        }
    }
    match out.len() {
        0 => Prop::Const(false),
        1 => out.pop().expect("one part"),
        _ => Prop::Or(out),
    }
}

fn iff(a: Prop, b: Prop) -> Prop {
    disj(vec![
        conj(vec![a.clone(), b.clone()]),
        conj(vec![neg(a), neg(b)]),
    ])
}

// --- grounding --------------------------------------------------------------

/// A concrete predicate argument: an element of a carrier, or a subset of a
/// carrier product (its member points, in domain order).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Val {
    Elem(usize),
    Set(Vec<Vec<usize>>),
}

/// The interpretation of each predicate: the argument tuples where it holds.
pub type Tables = BTreeMap<String, BTreeSet<Vec<Val>>>;

/// Each unary function's output at domain indices `0, …, size(domain)-1`.
pub type FunctionTables = BTreeMap<String, Vec<usize>>;

/// A finite model: carrier sizes (in carrier order), constants and tables.
#[derive(Clone, Debug)]
pub struct Model {
    pub sizes: Vec<(String, usize)>,
    pub constants: HashMap<String, usize>,
    pub tables: Tables,
    pub functions: FunctionTables,
}

impl Model {
    fn size(&self, carrier: &str) -> usize {
        size_of(&self.sizes, carrier)
    }
}

fn size_of(sizes: &[(String, usize)], carrier: &str) -> usize {
    sizes
        .iter()
        .find(|(name, _)| name == carrier)
        .map_or(0, |(_, size)| *size)
}

/// Mixed-radix tuples, last position fastest. Holding only the next tuple
/// avoids materializing every possible function interpretation at once.
struct Assignments {
    lengths: Vec<usize>,
    next: Option<Vec<usize>>,
}

impl Assignments {
    fn new(lengths: &[usize]) -> Self {
        Self {
            lengths: lengths.to_vec(),
            next: (!lengths.contains(&0)).then(|| vec![0; lengths.len()]),
        }
    }
}

impl Iterator for Assignments {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.next.take()?;
        let mut following = current.clone();
        for index in (0..following.len()).rev() {
            if following[index] + 1 < self.lengths[index] {
                following[index] += 1;
                self.next = Some(following);
                break;
            }
            following[index] = 0;
        }
        Some(current)
    }
}

/// Every index tuple of `lengths`, in the historical search order.
fn product(lengths: &[usize]) -> Vec<Vec<usize>> {
    Assignments::new(lengths).collect()
}

struct FunctionLayout<'s> {
    rows: Vec<(&'s UnaryFunction, usize)>,
    lengths: Vec<usize>,
}

fn checked_power(mut base: usize, mut exponent: usize) -> Option<usize> {
    let mut result = 1usize;
    while exponent != 0 {
        if exponent % 2 == 1 {
            result = result.checked_mul(base)?;
        }
        exponent /= 2;
        if exponent != 0 {
            base = base.checked_mul(base)?;
        }
    }
    Some(result)
}

fn function_layout<'s>(
    skeleton: &'s Skeleton,
    sizes: &[(String, usize)],
) -> Result<FunctionLayout<'s>, String> {
    let mut rows = Vec::new();
    let mut cells = 0usize;
    let mut cardinality = 1usize;
    for function in &skeleton.functions {
        let domain = size_of(sizes, &function.domain);
        let codomain = size_of(sizes, &function.codomain);
        if domain == 0 || codomain == 0 {
            return Err(format!(
                "function {} has a missing or empty carrier",
                function.name
            ));
        }
        cells = cells
            .checked_add(domain)
            .ok_or("function table dimensions overflow")?;
        if cells
            .checked_mul(std::mem::size_of::<usize>())
            .is_none_or(|bytes| bytes > isize::MAX as usize)
        {
            return Err("function table dimensions exceed addressable storage".into());
        }
        cardinality = cardinality
            .checked_mul(
                checked_power(codomain, domain)
                    .ok_or("function interpretation cardinality overflows")?,
            )
            .ok_or("combined function interpretation cardinality overflows")?;
        rows.push((function, domain));
    }
    let mut lengths = Vec::new();
    lengths
        .try_reserve_exact(cells)
        .map_err(|error| format!("cannot allocate function table dimensions: {error}"))?;
    for (function, domain) in &rows {
        lengths.extend(std::iter::repeat_n(
            size_of(sizes, &function.codomain),
            *domain,
        ));
    }
    Ok(FunctionLayout { rows, lengths })
}

fn check_function_tables(skeleton: &Skeleton, model: &Model) -> Result<(), String> {
    if model.functions.len() != skeleton.functions.len() {
        return Err("model function tables do not match the declared functions".into());
    }
    for function in &skeleton.functions {
        let domain = model.size(&function.domain);
        let codomain = model.size(&function.codomain);
        let table = model
            .functions
            .get(&function.name)
            .ok_or_else(|| format!("missing table for function {}", function.name))?;
        if domain == 0 || codomain == 0 || table.len() != domain {
            return Err(format!(
                "invalid table dimensions for function {}",
                function.name
            ));
        }
        if table.iter().any(|value| *value >= codomain) {
            return Err(format!(
                "function {} has an output outside its codomain",
                function.name
            ));
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum Bound {
    Elem(usize),
    Truth(bool),
}

enum TermValue {
    Elem(usize),
    /// A predicate-valued term: its ground formula at each point.
    Lam(Vec<(Vec<usize>, Prop)>),
}

enum Atoms<'m> {
    /// Encoding: each atom becomes a propositional variable, numbered from 1
    /// in the order it is first met.
    Encode(HashMap<(String, Vec<Val>), usize>, Vec<(String, Vec<Val>)>),
    /// Evaluation in a concrete model.
    Eval(&'m Tables),
}

struct Grounding<'s, 'm> {
    skeleton: &'s Skeleton,
    sizes: &'m [(String, usize)],
    constants: &'m HashMap<String, usize>,
    functions: &'m FunctionTables,
    atoms: Atoms<'m>,
}

impl Grounding<'_, '_> {
    fn size(&self, carrier: &str) -> Result<usize, String> {
        self.sizes
            .iter()
            .find(|(name, _)| name == carrier)
            .map(|(_, size)| *size)
            .ok_or_else(|| format!("unknown carrier {carrier}"))
    }

    fn domain(&self, sorts: &[String]) -> Result<Vec<Vec<usize>>, String> {
        let lengths = sorts
            .iter()
            .map(|sort| self.size(sort))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(product(&lengths))
    }

    /// The concrete values of an argument sort: elements, or every subset.
    fn values(&self, sort: &Sort) -> Result<Vec<Val>, String> {
        match sort {
            Sort::Carrier(carrier) => Ok((0..self.size(carrier)?).map(Val::Elem).collect()),
            Sort::Set(carriers) => {
                let points = self.domain(carriers)?;
                Ok(product(&vec![2; points.len()])
                    .into_iter()
                    .map(|bits| {
                        Val::Set(
                            points
                                .iter()
                                .zip(bits)
                                .filter(|(_, bit)| *bit == 1)
                                .map(|(point, _)| point.clone())
                                .collect(),
                        )
                    })
                    .collect())
            }
        }
    }

    fn atom(&mut self, pred: &str, args: Vec<Val>) -> Prop {
        match &mut self.atoms {
            Atoms::Encode(index, order) => {
                let key = (pred.to_owned(), args);
                let next = index.len() + 1;
                let var = *index.entry(key.clone()).or_insert_with(|| {
                    order.push(key);
                    next
                });
                Prop::Var(var)
            }
            Atoms::Eval(tables) => Prop::Const(tables.get(pred).is_some_and(|t| t.contains(&args))),
        }
    }

    fn term(&mut self, t: &Term, env: &[(String, Bound)]) -> Result<TermValue, String> {
        match t {
            Term::Var(name) => match lookup(env, name) {
                Some(Bound::Elem(value)) => Ok(TermValue::Elem(value)),
                Some(Bound::Truth(_)) => {
                    Err(format!("propositional variable {name} used as a term"))
                }
                None => self
                    .constants
                    .get(name)
                    .map(|value| TermValue::Elem(*value))
                    .ok_or_else(|| format!("unknown term {name}")),
            },
            Term::App(name, argument) => {
                let TermValue::Elem(argument) = self.term(argument, env)? else {
                    return Err(format!("function {name} requires a carrier element"));
                };
                let function = self
                    .skeleton
                    .functions
                    .iter()
                    .find(|function| function.name == *name)
                    .ok_or_else(|| format!("unknown function {name}"))?;
                if argument >= self.size(&function.domain)? {
                    return Err(format!(
                        "function {name} has an argument outside its domain"
                    ));
                }
                let value = self
                    .functions
                    .get(name)
                    .and_then(|table| table.get(argument))
                    .ok_or_else(|| format!("incomplete table for function {name}"))?;
                if *value >= self.size(&function.codomain)? {
                    return Err(format!(
                        "function {name} has an output outside its codomain"
                    ));
                }
                Ok(TermValue::Elem(*value))
            }
            Term::Lam(vars, body) => {
                let sorts: Vec<String> = vars.iter().map(|(_, sort)| sort.clone()).collect();
                let mut out = Vec::new();
                for point in self.domain(&sorts)? {
                    let mut inner = env.to_vec();
                    inner.extend(
                        vars.iter()
                            .zip(&point)
                            .map(|((name, _), value)| (name.clone(), Bound::Elem(*value))),
                    );
                    let formula = self.formula(body, &inner)?;
                    out.push((point, formula));
                }
                Ok(TermValue::Lam(out))
            }
        }
    }

    fn formula(&mut self, f: &Formula, env: &[(String, Bound)]) -> Result<Prop, String> {
        Ok(match f {
            Formula::True => Prop::Const(true),
            Formula::False => Prop::Const(false),
            Formula::Not(a) => neg(self.formula(a, env)?),
            Formula::Binary(connective, a, b) => {
                let a = self.formula(a, env)?;
                let b = self.formula(b, env)?;
                match connective {
                    Connective::And => conj(vec![a, b]),
                    Connective::Or => disj(vec![a, b]),
                    Connective::Imp => disj(vec![neg(a), b]),
                    Connective::Iff => iff(a, b),
                }
            }
            Formula::Quantifier {
                exists,
                var,
                sort,
                body,
            } => {
                let values: Vec<Bound> = match sort {
                    None => vec![Bound::Truth(false), Bound::Truth(true)],
                    Some(sort) => (0..self.size(sort)?).map(Bound::Elem).collect(),
                };
                let mut parts = Vec::new();
                for value in values {
                    let mut inner = env.to_vec();
                    inner.push((var.clone(), value));
                    parts.push(self.formula(body, &inner)?);
                }
                if *exists { disj(parts) } else { conj(parts) }
            }
            Formula::Eq(a, b) => match (self.term(a, env)?, self.term(b, env)?) {
                (TermValue::Elem(a), TermValue::Elem(b)) => Prop::Const(a == b),
                _ => return Err("equation between predicate-valued terms".into()),
            },
            Formula::Atom(pred, args) => {
                if let Some(bound) = lookup(env, pred) {
                    // a bound propositional variable
                    return match bound {
                        Bound::Truth(value) => Ok(Prop::Const(value)),
                        Bound::Elem(_) => Err(format!("element variable {pred} used as a formula")),
                    };
                }
                let values = args
                    .iter()
                    .map(|t| self.term(t, env))
                    .collect::<Result<Vec<_>, _>>()?;
                self.apply(pred, values)?
            }
        })
    }

    /// `pred(args)`; a predicate-valued argument is matched against every
    /// concrete subset of its sort.
    fn apply(&mut self, pred: &str, args: Vec<TermValue>) -> Result<Prop, String> {
        let sorts = self
            .skeleton
            .predicates
            .iter()
            .find(|(name, _)| name == pred)
            .map(|(_, sorts)| sorts.clone())
            .ok_or_else(|| format!("unknown predicate {pred}"))?;
        let mut options: Vec<Vec<(Val, Prop)>> = Vec::new();
        for (sort, arg) in sorts.iter().zip(args) {
            match arg {
                TermValue::Lam(table) => {
                    let mut choices = Vec::new();
                    for subset in self.values(sort)? {
                        let Val::Set(members) = &subset else {
                            return Err(format!("{pred} takes an element, not a predicate"));
                        };
                        let condition = conj(
                            table
                                .iter()
                                .map(|(point, f)| {
                                    if members.contains(point) {
                                        f.clone()
                                    } else {
                                        neg(f.clone())
                                    }
                                })
                                .collect(),
                        );
                        choices.push((subset, condition));
                    }
                    options.push(choices);
                }
                TermValue::Elem(value) => options.push(vec![(Val::Elem(value), Prop::Const(true))]),
            }
        }
        let lengths: Vec<usize> = options.iter().map(Vec::len).collect();
        let mut parts = Vec::new();
        for combo in product(&lengths) {
            let mut conditions = Vec::new();
            let mut values = Vec::new();
            for (choices, index) in options.iter().zip(combo) {
                let (value, condition) = &choices[index];
                conditions.push(condition.clone());
                values.push(value.clone());
            }
            conditions.push(self.atom(pred, values));
            parts.push(conj(conditions));
        }
        Ok(disj(parts))
    }
}

fn lookup(env: &[(String, Bound)], name: &str) -> Option<Bound> {
    env.iter()
        .rev()
        .find(|(bound, _)| bound == name)
        .map(|(_, value)| *value)
}

// --- CNF and DPLL ------------------------------------------------------------

/// A literal equivalent to `f`, adding its defining clauses.
fn tseitin(f: &Prop, clauses: &mut Vec<Vec<i64>>, counter: &mut usize) -> i64 {
    match f {
        Prop::Var(var) => *var as i64,
        Prop::Not(inner) => -tseitin(inner, clauses, counter),
        Prop::And(parts) | Prop::Or(parts) => {
            let lits: Vec<i64> = parts.iter().map(|g| tseitin(g, clauses, counter)).collect();
            *counter += 1;
            let x = *counter as i64;
            if matches!(f, Prop::And(_)) {
                clauses.extend(lits.iter().map(|lit| vec![-x, *lit]));
                clauses.push(std::iter::once(x).chain(lits.iter().map(|l| -l)).collect());
            } else {
                clauses.push(std::iter::once(-x).chain(lits.iter().copied()).collect());
                clauses.extend(lits.iter().map(|lit| vec![x, -lit]));
            }
            x
        }
        Prop::Const(_) => unreachable!("constants fold away before encoding"),
    }
}

/// DPLL with unit propagation and chronological backtracking. Branches on
/// the `prefer` variables first, in order, each false first; `None` when the
/// clauses are unsatisfiable. The result is indexed by variable (index 0
/// unused).
pub fn solve(clauses: &[Vec<i64>], nvars: usize, prefer: &[usize]) -> Option<Vec<bool>> {
    let preferred: BTreeSet<usize> = prefer.iter().copied().collect();
    let order: Vec<usize> = prefer
        .iter()
        .copied()
        .chain((1..=nvars).filter(|v| !preferred.contains(v)))
        .collect();
    // 0 unassigned, 1 true, -1 false
    let mut assign = vec![0i8; nvars + 1];
    let mut trail: Vec<usize> = Vec::new();
    // (variable, trail length before it, whether true was tried)
    let mut decisions: Vec<(usize, usize, bool)> = Vec::new();
    let value = |assign: &[i8], lit: i64| -> i8 {
        let v = assign[lit.unsigned_abs() as usize];
        if lit > 0 { v } else { -v }
    };
    let propagate = |assign: &mut Vec<i8>, trail: &mut Vec<usize>| -> bool {
        let mut changed = true;
        while changed {
            changed = false;
            for clause in clauses {
                let mut unassigned = 0i64;
                let mut count = 0;
                let mut sat = false;
                for &lit in clause {
                    match value(assign, lit) {
                        1 => {
                            sat = true;
                            break;
                        }
                        0 => {
                            count += 1;
                            unassigned = lit;
                        }
                        _ => {}
                    }
                }
                if sat {
                    continue;
                }
                if count == 0 {
                    return false;
                }
                if count == 1 {
                    let var = unassigned.unsigned_abs() as usize;
                    assign[var] = if unassigned > 0 { 1 } else { -1 };
                    trail.push(var);
                    changed = true;
                }
            }
        }
        true
    };
    loop {
        if propagate(&mut assign, &mut trail) {
            match order.iter().find(|&&v| assign[v] == 0) {
                None => return Some(assign.iter().map(|&v| v == 1).collect()),
                Some(&var) => {
                    decisions.push((var, trail.len(), false));
                    assign[var] = -1;
                    trail.push(var);
                }
            }
            continue;
        }
        loop {
            let (var, mark, tried_true) = decisions.pop()?;
            for undone in trail.drain(mark..) {
                assign[undone] = 0;
            }
            if !tried_true {
                decisions.push((var, mark, true));
                assign[var] = 1;
                trail.push(var);
                break;
            }
        }
    }
}

// --- search -----------------------------------------------------------------

/// Every carrier-size assignment up to `max_size`, smallest total first.
pub fn size_assignments(carriers: &[String], max_size: usize) -> Vec<Vec<(String, usize)>> {
    let mut combos = product(&vec![max_size; carriers.len()]);
    for combo in &mut combos {
        for size in combo.iter_mut() {
            *size += 1;
        }
    }
    combos.sort_by(|a, b| (a.iter().sum::<usize>(), a).cmp(&(b.iter().sum::<usize>(), b)));
    combos
        .into_iter()
        .map(|combo| carriers.iter().cloned().zip(combo).collect())
        .collect()
}

/// The smallest model (by total carrier size) in which every `holds`
/// formula is true and every `fails` formula false; `None` within the bound.
pub fn find_model(
    skeleton: &Skeleton,
    holds: &[&Formula],
    fails: &[&Formula],
    max_size: usize,
) -> Result<Option<Model>, String> {
    for sizes in size_assignments(&skeleton.carriers, max_size) {
        let layout = function_layout(skeleton, &sizes)?;
        let names: Vec<&String> = skeleton.constants.iter().map(|(name, _)| name).collect();
        let lengths: Vec<usize> = skeleton
            .constants
            .iter()
            .map(|(_, sort)| size_of(&sizes, sort))
            .collect();
        for values in product(&lengths) {
            let constants: HashMap<String, usize> =
                names.iter().map(|n| (*n).clone()).zip(values).collect();
            for outputs in Assignments::new(&layout.lengths) {
                let mut outputs = outputs.into_iter();
                let functions: FunctionTables = layout
                    .rows
                    .iter()
                    .map(|(function, domain)| {
                        (
                            function.name.clone(),
                            outputs.by_ref().take(*domain).collect(),
                        )
                    })
                    .collect();
                let mut g = Grounding {
                    skeleton,
                    sizes: &sizes,
                    constants: &constants,
                    functions: &functions,
                    atoms: Atoms::Encode(HashMap::new(), Vec::new()),
                };
                let mut parts = Vec::new();
                for f in holds {
                    parts.push(g.formula(f, &[])?);
                }
                for f in fails {
                    parts.push(neg(g.formula(f, &[])?));
                }
                let target = conj(parts);
                let Atoms::Encode(_, order) = g.atoms else {
                    unreachable!("encoding")
                };
                let atom_count = order.len();
                let mut clauses = Vec::new();
                let nvars = match target {
                    Prop::Const(false) => continue,
                    Prop::Const(true) => atom_count,
                    target => {
                        let mut counter = atom_count;
                        let top = tseitin(&target, &mut clauses, &mut counter);
                        clauses.push(vec![top]);
                        counter
                    }
                };
                let prefer: Vec<usize> = (1..=atom_count).collect();
                let Some(assignment) = solve(&clauses, nvars, &prefer) else {
                    continue;
                };
                let mut tables: Tables = skeleton
                    .predicates
                    .iter()
                    .map(|(name, _)| (name.clone(), BTreeSet::new()))
                    .collect();
                for (index, (pred, args)) in order.into_iter().enumerate() {
                    if assignment[index + 1] {
                        tables.entry(pred).or_default().insert(args);
                    }
                }
                let model = Model {
                    sizes: sizes.clone(),
                    constants,
                    tables,
                    functions,
                };
                check_function_tables(skeleton, &model)?;
                for f in holds {
                    if !evaluate(skeleton, &model, f)? {
                        return Err("solver model does not satisfy its own encoding".into());
                    }
                }
                for f in fails {
                    if evaluate(skeleton, &model, f)? {
                        return Err("solver model does not satisfy its own encoding".into());
                    }
                }
                return Ok(Some(model));
            }
        }
    }
    Ok(None)
}

/// Direct evaluation of a formula in a concrete model (independent of the CNF).
pub fn evaluate(skeleton: &Skeleton, model: &Model, f: &Formula) -> Result<bool, String> {
    check_function_tables(skeleton, model)?;
    let mut g = Grounding {
        skeleton,
        sizes: &model.sizes,
        constants: &model.constants,
        functions: &model.functions,
        atoms: Atoms::Eval(&model.tables),
    };
    match g.formula(f, &[])? {
        Prop::Const(value) => Ok(value),
        other => Err(format!("evaluation left a symbolic formula: {other:?}")),
    }
}

/// One search target: the omitted premise (`None` for the joint witness),
/// the formulas that must hold and those that must fail.
pub struct Target<'s> {
    pub omitted: Option<&'s str>,
    pub holds: Vec<&'s Formula>,
    pub fails: Vec<&'s Formula>,
}

/// The omission targets for `omit` (premise names; every premise if `None`),
/// in premise order.
pub fn omission_targets<'s>(skeleton: &'s Skeleton, omit: Option<&[String]>) -> Vec<Target<'s>> {
    skeleton
        .premises
        .iter()
        .enumerate()
        .filter(|(_, p)| omit.is_none_or(|omit| omit.contains(&p.name)))
        .map(|(index, p)| Target {
            omitted: Some(&p.name),
            holds: skeleton
                .premises
                .iter()
                .enumerate()
                .filter(|(other, _)| *other != index)
                .map(|(_, q)| &q.formula)
                .collect(),
            fails: vec![&skeleton.conclusion],
        })
        .collect()
}

// --- Lean rendering ------------------------------------------------------------

fn lean_type(sort: &Sort) -> String {
    match sort {
        Sort::Carrier(carrier) => carrier.clone(),
        Sort::Set(carriers) => format!("({} → Prop)", carriers.join(" → ")),
    }
}

fn render_predicate(
    name: &str,
    sorts: &[Sort],
    table: &BTreeSet<Vec<Val>>,
    model: &Model,
) -> String {
    if sorts.is_empty() {
        let body = if table.is_empty() { "False" } else { "True" };
        return format!("abbrev {name} : Prop := {body}");
    }
    let params: Vec<String> = (0..sorts.len()).map(|i| format!("x{i}")).collect();
    let signature = sorts
        .iter()
        .map(lean_type)
        .chain(["Prop".to_owned()])
        .collect::<Vec<_>>()
        .join(" → ");
    let total: u128 = sorts
        .iter()
        .map(|sort| match sort {
            Sort::Carrier(carrier) => model.size(carrier) as u128,
            Sort::Set(carriers) => {
                let points: u32 = carriers.iter().map(|c| model.size(c) as u32).product();
                1u128.checked_shl(points).unwrap_or(u128::MAX)
            }
        })
        .product();
    if table.is_empty() || table.len() as u128 == total {
        let body = if table.is_empty() { "False" } else { "True" };
        let blanks = vec!["_"; sorts.len()].join(" ");
        return format!("abbrev {name} : {signature} := fun {blanks} => {body}");
    }
    let rows: Vec<String> = table
        .iter()
        .map(|row| {
            let mut parts = Vec::new();
            for ((var, sort), value) in params.iter().zip(sorts).zip(row) {
                match (sort, value) {
                    (Sort::Carrier(_), Val::Elem(value)) => parts.push(format!("{var} = {value}")),
                    (Sort::Set(carriers), Val::Set(members)) => {
                        let lengths: Vec<usize> = carriers.iter().map(|c| model.size(c)).collect();
                        for point in product(&lengths) {
                            let coordinates: Vec<String> =
                                point.iter().map(usize::to_string).collect();
                            let app = format!("{var} {}", coordinates.join(" "));
                            parts.push(if members.contains(&point) {
                                app
                            } else {
                                format!("¬ {app}")
                            });
                        }
                    }
                    _ => parts.push(format!("{var} = ?")),
                }
            }
            format!("({})", parts.join(" ∧ "))
        })
        .collect();
    let head = format!("abbrev {name} : {signature} := fun {} =>", params.join(" "));
    if rows.len() == 1 {
        format!("{head} {}", rows[0])
    } else {
        format!("{head}\n  {}", rows.join(" ∨\n  "))
    }
}

fn render_function(function: &UnaryFunction, table: &[usize]) -> String {
    let (last, earlier) = table
        .split_last()
        .expect("nonempty function table of a valid finite model");
    let signature = format!("{} → {}", function.domain, function.codomain);
    if earlier.iter().all(|value| value == last) {
        return format!("abbrev {} : {signature} := fun _ => {last}", function.name);
    }
    let mut body = last.to_string();
    for (index, value) in earlier.iter().enumerate().rev() {
        body = format!("if x = {index} then {value} else {body}");
    }
    format!("abbrev {} : {signature} := fun x => {body}", function.name)
}

/// A valid model as Lean `abbrev`s: carriers, constants, functions, predicates.
/// `find_model` produces valid tables; `evaluate` checks externally supplied
/// function tables before evaluating a formula.
pub fn render_model(skeleton: &Skeleton, model: &Model) -> Vec<String> {
    let mut lines: Vec<String> = skeleton
        .carriers
        .iter()
        .map(|c| format!("abbrev {c} := Fin {}", model.size(c)))
        .collect();
    for (name, sort) in &skeleton.constants {
        lines.push(format!(
            "abbrev {name} : {sort} := {}",
            model.constants[name]
        ));
    }
    for function in &skeleton.functions {
        lines.push(render_function(function, &model.functions[&function.name]));
    }
    let empty = BTreeSet::new();
    for (name, sorts) in &skeleton.predicates {
        let table = model.tables.get(name).unwrap_or(&empty);
        lines.push(render_predicate(name, sorts, table, model));
    }
    lines
}

/// A `namespace label` with the model and its `certificate` theorem: the
/// omitted premise fails (or, for the witness, everything holds), the other
/// premises hold and the conclusion fails, by `delta …; decide`.
pub fn render_certificate(
    skeleton: &Skeleton,
    label: &str,
    model: &Model,
    omitted: Option<&str>,
) -> String {
    let mut conjuncts: Vec<String> = skeleton
        .premises
        .iter()
        .map(|p| {
            let text = format!("({})", p.lean);
            if Some(p.name.as_str()) == omitted {
                format!("¬ {text}")
            } else {
                text
            }
        })
        .collect();
    let conclusion = format!("({})", skeleton.conclusion_lean);
    conjuncts.push(match omitted {
        None => conclusion,
        Some(_) => format!("¬ {conclusion}"),
    });
    let statement = conjuncts.join(" ∧\n    ");
    let what = match omitted {
        Some(name) => format!(
            "Omission model for `{name}`: the other premises hold and the conclusion fails."
        ),
        None => "Joint witness: every premise and the conclusion hold.".to_owned(),
    };
    let delta = if skeleton.unfolded.is_empty() {
        String::new()
    } else {
        format!("  delta {}\n", skeleton.unfolded.join(" "))
    };
    // One `decide` per conjunct keeps each Decidable instance problem small.
    let holes = vec!["?_"; conjuncts.len()].join(", ");
    // `∀ P : Prop, P ∨ ¬ P` is not decidable; it is closed by `Classical.em`.
    let closer = if skeleton.quantifies_over_prop() {
        "first | decide | exact Classical.em"
    } else {
        "decide"
    };
    let mut lines = vec![
        format!("namespace {label}"),
        format!("/-! {what} Candidate from `truth countermodel`; checked by `decide`. -/"),
    ];
    lines.extend(render_model(skeleton, model));
    lines.push(format!("theorem certificate :\n    {statement} := by"));
    lines.push(format!("{delta}  refine ⟨{holes}⟩ <;> {closer}"));
    lines.push(format!("end {label}"));
    lines.join("\n")
}

// --- reports -------------------------------------------------------------------

/// The outcome for one omission target or the joint witness.
#[derive(Clone, Debug)]
pub struct Report {
    pub omitted: Option<String>,
    pub max_size: usize,
    /// `lean-checked`, `lean-rejected`, `candidate` or `unresolved`.
    pub status: &'static str,
    pub note: Option<String>,
    pub sizes: Option<Vec<(String, usize)>>,
    pub lean: Option<String>,
    pub lean_output: Option<String>,
}

impl Report {
    pub fn kind(&self) -> &'static str {
        if self.omitted.is_some() {
            "omission"
        } else {
            "witness"
        }
    }

    pub fn to_json(&self) -> Value {
        let mut out = Map::new();
        out.insert("omitted".into(), json!(self.omitted));
        out.insert("kind".into(), json!(self.kind()));
        out.insert("max_size".into(), json!(self.max_size));
        out.insert("status".into(), json!(self.status));
        if let Some(note) = &self.note {
            out.insert("note".into(), json!(note));
        }
        if let Some(sizes) = &self.sizes {
            let sizes: Map<String, Value> = sizes
                .iter()
                .map(|(carrier, size)| (carrier.clone(), json!(size)))
                .collect();
            out.insert("sizes".into(), Value::Object(sizes));
        }
        if let Some(lean) = &self.lean {
            out.insert("lean".into(), json!(lean));
        }
        if let Some(output) = &self.lean_output {
            out.insert("lean_output".into(), json!(output));
        }
        Value::Object(out)
    }

    /// The human-readable block: a status comment, then note, certificate
    /// and any Lean output.
    pub fn to_text(&self) -> String {
        let mut head = match &self.omitted {
            Some(name) => format!("-- {} {name}: {}", self.kind(), self.status),
            None => format!("-- {}: {}", self.kind(), self.status),
        };
        if let Some(sizes) = &self.sizes {
            let shown: Vec<String> = sizes
                .iter()
                .map(|(carrier, size)| format!("{carrier}: {size}"))
                .collect();
            head.push_str(&format!(" (sizes {})", shown.join(", ")));
        }
        let mut lines = vec![head];
        if let Some(note) = &self.note {
            lines.push(format!("-- {note}"));
        }
        if let Some(lean) = &self.lean {
            lines.push(lean.clone());
        }
        if let Some(output) = &self.lean_output {
            lines.push(format!("/- Lean output:\n{output}\n-/"));
        }
        lines.join("\n")
    }
}

/// Lean's verdict on a snippet appended to the theorem's module: accepted,
/// and the output.
pub type Checker<'c> = &'c dyn Fn(&Skeleton, &str) -> (bool, String);

/// Searches every omission target for `omit` (all premises if `None`), plus
/// the joint witness if `witness`, and has `check` (if any) verify the
/// candidates: one Lean run for all, and each alone only when that fails.
pub fn run(
    skeleton: &Skeleton,
    omit: Option<&[String]>,
    max_size: usize,
    witness: bool,
    check: Option<Checker>,
) -> Result<Vec<Report>, String> {
    let short = skeleton
        .theorem
        .rsplit('.')
        .next()
        .unwrap_or(&skeleton.theorem);
    let mut targets = omission_targets(skeleton, omit);
    if witness {
        targets.push(Target {
            omitted: None,
            holds: skeleton
                .premises
                .iter()
                .map(|p| &p.formula)
                .chain([&skeleton.conclusion])
                .collect(),
            fails: Vec::new(),
        });
    }
    let mut reports = Vec::new();
    for target in targets {
        let label = format!(
            "Countermodel.{short}.{}",
            target
                .omitted
                .map_or_else(|| "witness".to_owned(), |name| format!("omit_{name}"))
        );
        let mut report = Report {
            omitted: target.omitted.map(str::to_owned),
            max_size,
            status: "unresolved",
            note: None,
            sizes: None,
            lean: None,
            lean_output: None,
        };
        match find_model(skeleton, &target.holds, &target.fails, max_size)? {
            None => {
                let mut note = format!(
                    "no model with carriers of size ≤ {max_size}; this does not show the premise is needed"
                );
                if let Some(name) = target.omitted {
                    let premise = skeleton
                        .premises
                        .iter()
                        .find(|p| p.name == name)
                        .expect("omitted premise");
                    if find_model(skeleton, &[], &[&premise.formula], max_size)?.is_none() {
                        note.push_str(
                            " (the premise itself holds in every model within these bounds)",
                        );
                    }
                }
                report.note = Some(note);
            }
            Some(model) => {
                report.status = "candidate";
                report.lean = Some(render_certificate(skeleton, &label, &model, target.omitted));
                report.sizes = Some(model.sizes);
            }
        }
        reports.push(report);
    }
    if let Some(check) = check {
        let snippets: Vec<&str> = reports
            .iter()
            .filter(|r| r.status == "candidate")
            .filter_map(|r| r.lean.as_deref())
            .collect();
        if !snippets.is_empty() {
            let (all_ok, _) = check(skeleton, &snippets.join("\n\n"));
            for report in reports.iter_mut().filter(|r| r.status == "candidate") {
                if !all_ok {
                    let (ok, output) = check(skeleton, report.lean.as_deref().unwrap_or_default());
                    if !ok {
                        report.lean_output = Some(output);
                    }
                }
                report.status = if report.lean_output.is_none() {
                    "lean-checked"
                } else {
                    "lean-rejected"
                };
            }
        }
    }
    Ok(reports)
}

/// The premise names `omit` selects: binder names, or 1-based positions.
pub fn resolve_omit(skeleton: &Skeleton, omit: &[String]) -> Result<Vec<String>, String> {
    let names = skeleton.premise_names();
    let resolved: Vec<String> = omit
        .iter()
        .map(|o| match o.parse::<usize>() {
            Ok(position)
                if o.bytes().all(|b| b.is_ascii_digit())
                    && (1..=names.len()).contains(&position) =>
            {
                names[position - 1].to_owned()
            }
            _ => o.clone(),
        })
        .collect();
    let unknown: Vec<&String> = resolved
        .iter()
        .filter(|o| !names.contains(&o.as_str()))
        .collect();
    if unknown.is_empty() {
        Ok(resolved)
    } else {
        Err(format!(
            "unknown premise {unknown:?}; premises are {names:?}"
        ))
    }
}

// --- Lean ---------------------------------------------------------------------

/// `lake <args>` through `scripts/worker_env.py`, bounded by `timeout`.
fn lake(root: &Path, tail: &[&str], timeout: Duration) -> Result<Finished, String> {
    let args: Vec<String> = ["scripts/worker_env.py", "--", "lake"]
        .iter()
        .chain(tail)
        .map(|part| part.to_string())
        .collect();
    structure::run_bounded(root, "python3", &args, timeout)?.ok_or_else(|| {
        format!(
            "`lake {}` timed out after {}s",
            tail.join(" "),
            timeout.as_secs()
        )
    })
}

fn detail(finished: &Finished) -> String {
    let stderr = finished.stderr.trim();
    if stderr.is_empty() {
        finished.stdout.trim().to_owned()
    } else {
        stderr.to_owned()
    }
}

fn scratch(prefix: &str) -> std::path::PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_nanos());
    std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()))
}

/// The module declaring `theorem`; a Challenge/Solution pair resolves to
/// the Solution.
pub fn locate(root: &Path, theorem: &str) -> Result<String, String> {
    let sources = Sources::scan(root)?;
    let modules = sources.modules_for(theorem);
    let solutions: Vec<&String> = modules
        .iter()
        .filter(|m| m.ends_with(".Solution"))
        .collect();
    if modules.len() > 1 && solutions.len() == 1 {
        return Ok(solutions[0].clone());
    }
    sources.module_for(theorem)
}

/// The elaborated first-order skeleton of `theorem` (Lake builds `module`
/// first, located from source when `None`).
pub fn extract(root: &Path, theorem: &str, module: Option<&str>) -> Result<Skeleton, String> {
    let module = match module {
        Some(module) => module.to_owned(),
        None => locate(root, theorem)?,
    };
    let built = lake(root, &["build", &module], BUILD_TIMEOUT)?;
    if !built.success {
        return Err(format!("build of {module} failed: {}", detail(&built)));
    }
    let input = scratch("truth-countermodel").with_extension("json");
    let request = json!({"modules": [module], "theorem": theorem});
    fs::write(&input, request.to_string()).map_err(|error| os_error(&error, &input))?;
    let input_text = input.display().to_string();
    let done = lake(
        root,
        &["env", "lean", "--run", EXTRACTOR, &input_text],
        EXTRACT_TIMEOUT,
    );
    let _ = fs::remove_file(&input);
    let done = done?;
    if !done.success {
        return Err(format!("extraction failed: {}", detail(&done)));
    }
    let value: Value = serde_json::from_str(done.stdout.trim()).map_err(|error| {
        format!(
            "extractor returned invalid JSON ({error}): {}",
            done.stdout.trim()
        )
    })?;
    Skeleton::parse(&value, &module)
}

/// Lean's verdict on `snippet` after `import <module>`: accepted (exit 0 and
/// no `error` in the output), and the output.
pub fn lean_check(root: &Path, skeleton: &Skeleton, snippet: &str) -> (bool, String) {
    let directory = scratch("truth-countermodel-check");
    let path = directory.join("CountermodelCheck.lean");
    let written = fs::create_dir_all(&directory)
        .and_then(|()| fs::write(&path, format!("import {}\n\n{snippet}\n", skeleton.module)));
    let result = match written {
        Err(error) => (false, os_error(&error, &path)),
        Ok(()) => match lake(
            root,
            &["env", "lean", &path.display().to_string()],
            CHECK_TIMEOUT,
        ) {
            Err(message) => (false, message),
            Ok(done) => {
                let output = format!("{}{}", done.stdout, done.stderr).trim().to_owned();
                (done.success && !output.contains("error"), output)
            }
        },
    };
    let _ = fs::remove_dir_all(&directory);
    result
}

#[cfg(test)]
mod tests;
