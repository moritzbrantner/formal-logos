module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Cast.Lemmas
public import TruthCore.Logic.InquiryPresuppositions
public import TruthCore.Results.Logic.EpistemicAccuracy.Refinement.Solution

/-! Exact finite fixtures for the actual-inquiry comparisons. Reports,
occurrences, reason status and the probability weights are separate inputs
where the corresponding comparison stipulates them. -/

@[expose] public section
namespace TruthCore.Logic.ActualInquiryControls

def bits : List Bool := [false, true]

def pairs (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x => ys.map (x, ·)

def masks (n : Nat) : List Nat := List.range (2 ^ n)

def selected (xs : List α) (mask : Nat) : List α :=
  (xs.zipIdx).filterMap fun (x, i) => if mask.testBit i then some x else none

def mass (rows : List (α × Nat)) (event : α → Bool) : Nat :=
  ((rows.filter fun r => event r.1).map Prod.snd).sum

def posterior (rows : List (α × Nat)) (target cond : α → Bool) : Option ℚ :=
  let den := mass rows cond
  if den = 0 then none else some ((mass rows (fun r => target r && cond r) : ℚ) / den)

def weighted (rows : List α) (base mask : Nat) : List (α × Nat) :=
  rows.zipIdx.map fun (r, i) => (r, mask / (base ^ i) % base)

namespace Parity

def labels : List Nat := [930, 932, 1007, 1987, 1989, 1990, 1991]
def paired : List (Nat × Nat) := [(930, 932), (1007, 1987), (1989, 1990)]
def residue : List Nat := [1991]
def rosters : List (List Nat) := (List.range 8).map labels.take

def report (r : List Nat) : Nat × Nat := (r.length / 2, r.length % 2)
def coarse (r : List Nat) : Nat := (report r).1
def odd (r : List Nat) : Bool := (report r).2 == 1
def full (r : List Nat) : Bool := report r == (3, 1)
def pair3 (r : List Nat) : Bool := coarse r == 3
def sixOrSeven (r : List Nat) : Bool := r.length == 6 || r.length == 7

def implication (p q : List Nat → Bool) : Bool :=
  rosters.any p && rosters.any (fun r => !q r) && rosters.all (fun r => !p r || q r)

def invariant [BEq E] (obs : List Nat → E) (q : List Nat → Bool) : Bool :=
  (pairs rosters rosters).all (fun (s, t) => obs s != obs t || q s == q t)

theorem pairingAndInformation :
    labels.eraseDups.length = labels.length ∧
    paired.flatMap (fun (x, y) => [x, y]) ++ residue = labels ∧
    paired.length = 3 ∧ residue.length = 1 ∧
    (rosters.filter pair3).map List.length = [6, 7] ∧
    (rosters.filter pair3).map odd = [false, true] ∧
    ([(full, odd), (odd, full), (pair3, odd), (pair3, fun r => !odd r), (pair3, sixOrSeven)].all
      fun (p, q) => rosters.any p && rosters.any (fun r => !q r)) ∧
    implication full odd ∧ ¬ implication odd full ∧ ¬ implication pair3 odd ∧
    ¬ implication pair3 (fun r => !odd r) ∧ implication pair3 sixOrSeven ∧
    ¬ invariant coarse odd ∧ invariant report odd ∧ invariant coarse sixOrSeven := by
  decide +kernel

def merits : Bool := rosters.all fun r => report r != report labels || odd r

/-- Profile 0 is aim-relative, 1 independent, and 2 without force.
The two entries are for the accuracy and comfort aims. -/
def force (profile : Fin 3) (accuracy : Bool) : Bool :=
  merits && (profile == 1 || (profile == 0 && accuracy))

theorem forceRows :
    merits ∧
    (List.finRange 3).map (fun i => (force i true, force i false)) =
      [(true, false), (true, true), (false, false)] := by
  decide +kernel

end Parity

namespace Episode

abbrev Case := Fin 3 × Bool × Bool
def worlds : List Case := (List.finRange 3).flatMap fun k => (pairs bits bits).map (k, ·)

def asks (w : Case) : Bool := w.1 == 1
def thought (w : Case) : Bool := w.1 != 0
def external (w : Case) : Bool := w.2.1
def marker (w : Case) : Bool := w.2.2

def actual : Case := (1, true, true)
def counterfeit : Case := (1, false, true)
def reportOnly : Case := (0, true, true)

theorem episodeRows :
    worlds.length = 12 ∧ asks actual ∧ thought actual ∧ external actual ∧ marker actual ∧
    asks counterfeit ∧ thought counterfeit ∧ ¬ external counterfeit ∧
    marker reportOnly ∧ ¬ asks reportOnly ∧ ¬ thought reportOnly ∧
    worlds.all (fun w => !asks w || thought w) ∧
    worlds.any (fun w => thought w && !asks w) ∧ worlds.any (fun w => !thought w) ∧
    worlds.any (fun w => marker w && !thought w) := by
  decide +kernel

def restrictions : List (List Case) :=
  let others := worlds.filter (· != actual)
  (masks others.length).map fun mask => actual :: selected others mask

def comparison (h : List Case) : Bool :=
  let fiber := h.filter asks
  !fiber.isEmpty && fiber.all thought && h.all (fun w => !asks w || thought w) &&
    (!h.contains counterfeit || (fiber.any external && fiber.any (fun w => !external w)))

set_option maxRecDepth 4096 in
theorem restrictionCensus :
    restrictions.length = 2048 ∧ (restrictions.filter (·.contains counterfeit)).length = 1024 ∧
    restrictions.all comparison := by
  decide +kernel

/-- P's external basis and Q's occurrence basis may be defeated independently. -/
def survive (extDefeat occDefeat targetQ : Bool) : Bool :=
  if targetQ then !occDefeat else !extDefeat

def reasons (e o calibrate q : Bool) : Bool := calibrate && survive e o q

theorem usesAndDefeat :
    (pairs (pairs bits bits) bits).length = 8 ∧
    ∀ e o calibrate : Bool, survive e o false = !e ∧ survive e o true = !o ∧
      (reasons e o calibrate false || reasons e o calibrate true) =
        (calibrate && (!e || !o)) ∧
      (e = true → o = false → calibrate = true →
        reasons e o calibrate false = false ∧ reasons e o calibrate true = true) := by
  decide +kernel

end Episode

namespace Phenomenal

abbrev Case := Fin 4 × Fin 4 × Bool × Bool

def phen (k : Fin 4) : Bool := 2 ≤ k.val
def thought (k : Fin 4) : Bool := k == 1 || k == 3

def primary (w : Case) : Bool := phen w.1
def challenge (w : Case) : Bool := phen w.2.1
def occurs (w : Case) : Bool := primary w || challenge w
def thinks (w : Case) : Bool := thought w.1 || thought w.2.1
def marker (w : Case) : Bool := w.2.2.1
def external (w : Case) : Bool := w.2.2.2

def worlds : List Case :=
  (pairs (List.finRange 4) (List.finRange 4)).flatMap fun (p, d) =>
    (pairs bits bits).map fun (m, q) => (p, d, m, q)

def assigned : List Case := [(3, 0, true, true), (2, 0, true, false), (0, 0, true, false),
  (0, 3, true, false), (0, 0, false, true)]

def varied (basis target : Case → Bool) : Bool :=
  worlds.any (fun w => basis w && target w) && worlds.any (fun w => basis w && !target w)

theorem occurrenceRows :
    worlds.length = 64 ∧ worlds.all (fun w => !(primary w || challenge w) || occurs w) ∧
    worlds.any (fun w => !primary w && challenge w && occurs w) ∧
    worlds.any (fun w => primary w && !thinks w) ∧
    worlds.any (fun w => thinks w && !occurs w) ∧
    worlds.any (fun w => marker w && !occurs w) ∧
    varied primary external ∧ varied primary thinks ∧ varied marker occurs ∧
    assigned.all worlds.contains := by
  decide +kernel

def bases : List (Case → Bool) := [primary, challenge, occurs]

def weights : List (List (Case × Nat)) :=
  (List.range (4 ^ 5)).map (weighted assigned 4)

def weightCheck (rows : List (Case × Nat)) : Bool :=
  let prior := posterior rows occurs (fun _ => true)
  (bases.all fun basis =>
    match posterior rows occurs basis, prior with
    | some post, some pre => post == 1 && decide (pre ≤ post) &&
      (decide (pre < post) == decide (pre < 1))
    | none, _ => true
    | _, none => false) &&
  (!(rows.all fun r => r.2 != 0) ||
    match posterior rows occurs marker with
    | none => false
    | some post => decide (0 < post ∧ post < 1))

set_option maxRecDepth 4096 in
theorem conditioning :
    weights.all weightCheck ∧
    (weights.map (fun rows => (bases.filter fun basis => mass rows basis != 0).length)).sum =
      2736 := by
  decide +kernel

def scores : List Int := [-2, -1, 0, 1, 2]
def admissibleScores : List (Int × Int × Int) :=
  ((pairs scores scores).flatMap fun (c, i) => scores.map (c, i, ·)).filter
    (fun (c, i, s) => decide (i ≤ s ∧ s ≤ c ∧ c ≠ i))

def scoreCases : List (Case × Int × Int × Int) :=
  pairs (worlds.filter (fun w => primary w || challenge w)) admissibleScores

theorem decisionScores :
    scoreCases.length = 1440 ∧ scoreCases.all
      (fun (w, c, i, s) => occurs w && decide (i < c ∧ s ≤ c)) ∧
    (pairs (pairs bits bits) bits).length = 8 ∧
    ∀ counts aims independent : Bool,
      (counts && (aims || independent) = true → counts = true) ∧
      (counts = true → aims = false → independent = false →
        (counts && (aims || independent)) = false) := by
  decide +kernel

end Phenomenal

end TruthCore.Logic.ActualInquiryControls

namespace TruthCore.Logic.ActualInquiryControls

namespace HigherOrder

structure Case where
  truth : Bool
  higher : Bool
  marker : Bool
  primary : Bool := false
  challenge : Bool := false

def both (c : Case) : Bool := c.higher && c.marker

def reportRows (a b : Nat) : List (Case × Nat) :=
  [(⟨true, true, true, false, false⟩, a), (⟨true, true, false, false, false⟩, 8 - a),
    (⟨false, true, true, false, false⟩, b), (⟨false, true, false, false, false⟩, 24 - b),
    (⟨true, false, true, false, false⟩, 18), (⟨true, false, false, false, false⟩, 6),
    (⟨false, false, true, false, false⟩, 2), (⟨false, false, false, false, false⟩, 6)]

def refineRows (rows : List (Case × Nat)) : List (Case × Nat) :=
  rows.flatMap fun (c, n) =>
    if c.truth && both c then
      [({ c with primary := true }, 1), ({ c with challenge := true }, 1)] ++
        (if 2 < n then [(c, n - 2)] else [])
    else [(c, n)]

def grounds : List (Case → Bool) :=
  [Case.primary, Case.challenge, fun c => c.primary || c.challenge]

def reportChecks (a b : Nat) (combined : ℚ) (relative : Ordering) : Bool :=
  let rows := reportRows a b
  let refined := refineRows rows
  rows.all (fun r => decide (0 < r.2)) &&
    (posterior rows Case.truth (fun _ => true) == some (1/2)) &&
    ((posterior rows Case.truth Case.marker).any fun q => decide (1/2 < q)) &&
    (posterior rows Case.truth Case.higher == some (1/4)) &&
    (posterior rows Case.truth both == some combined) &&
    decide (combined < 1/2) &&
    ((if combined < 1/4 then Ordering.lt else if combined = 1/4 then .eq else .gt) == relative) &&
    (posterior refined Case.truth both == some combined) &&
    (grounds.all fun e => posterior refined Case.truth (fun r => both r && e r) == some 1) &&
    refined.any (fun (r, _) => r.truth && !r.primary && r.challenge) &&
    refined.any (fun (r, _) => !r.truth && both r)

theorem reportControls :
    reportChecks 4 6 (2/5) .gt ∧ reportChecks 2 6 (1/4) .eq ∧
    reportChecks 2 12 (1/7) .lt := by
  decide +kernel

def roster : List Case :=
  [⟨true, true, false, true, false⟩, ⟨true, true, false, false, true⟩,
    ⟨true, true, false, false, false⟩, ⟨false, true, false, false, false⟩,
    ⟨true, false, false, true, false⟩, ⟨true, false, false, false, false⟩,
    ⟨false, false, false, false, false⟩]

structure Count where
  strict : Nat := 0
  saturated : Nat := 0
  zero : Nat := 0
  valid : Bool := true
  deriving DecidableEq

def countRestriction (rows : List (Case × Nat)) (h : Bool)
    (acc : Count) (e : Case → Bool) : Count :=
  let header := fun r => r.higher == h
  let reportMass := mass rows header
  let evidence := fun r => header r && e r
  let evidenceMass := mass rows evidence
  let reportTruth := mass rows (fun r => header r && r.truth)
  let evidenceTruth := mass rows (fun r => evidence r && r.truth)
  if reportMass = 0 then acc
  else if evidenceMass = 0 then { acc with zero := acc.zero + 1 }
  else if reportTruth = reportMass then
    { acc with saturated := acc.saturated + 1, valid := acc.valid && evidenceTruth == evidenceMass }
  else
    let valid := acc.valid && evidenceTruth == evidenceMass &&
      decide (reportTruth < reportMass) &&
      mass rows (fun r => evidence r && !r.truth) == 0 && decide (0 < evidenceTruth)
    { acc with strict := acc.strict + 1, valid := valid }

/-- A positive denominator makes the exact mass comparisons equivalent to
the posterior tests for zero, one and strict support below one. -/
theorem massComparisons (a b : ℕ) (positive : 0 < b) :
    ((a : ℚ) / b = 0 ↔ a = 0) ∧ ((a : ℚ) / b = 1 ↔ a = b) ∧
    ((a : ℚ) / b < 1 ↔ a < b) ∧ (0 < (a : ℚ) / b ↔ 0 < a) := by
  have hb : (0 : ℚ) < b := by exact_mod_cast positive
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_eq_iff hb.ne']
    simp
  · rw [div_eq_iff hb.ne']
    simp
  · rw [div_lt_iff₀ hb]
    simp
  · simpa using (div_pos_iff_of_pos_right (a := (a : ℚ)) hb)

def restrictionBlock (block : Nat) : Count :=
  (List.range 81).foldl (fun totals offset =>
      let rows := weighted roster 3 (block * 81 + offset)
      bits.foldl (fun acc h => grounds.foldl (countRestriction rows h) acc) totals) {}

def restrictionCounts : Count :=
  (List.range 27).foldl (fun acc block =>
    let next := restrictionBlock block
    ⟨acc.strict + next.strict, acc.saturated + next.saturated,
      acc.zero + next.zero, acc.valid && next.valid⟩) {}

set_option maxRecDepth 8192 in
theorem restrictions :
    restrictionCounts = ⟨5184, 2592, 5022, true⟩ ∧ 5184 + 2592 = 7776 := by
  decide +kernel

theorem reasonStatus : ∀ rq rh suspension warrant : Bool,
    let f6 := rq || rh
    (rh = true → f6 = true) ∧
    (rq = false → rh = false → suspension = true → f6 = false) ∧
    (rq = true → warrant = false → f6 = true) ∧
    (f6 = true ↔ rq = true ∨ rh = true) := by
  decide +kernel

/-- Each numerator ranges from zero to eight. Both likelihoods and their
difference are scaled by 64. The adverse-channel threshold comparisons
cross-multiply the positive denominator, avoiding rounded ratios. -/
def likelihoodSign (a t mq mn : Int) : Ordering × Bool :=
  let lq := a * t + (8 - a) * mq
  let ln := (8 - a) * mn
  let delta := mn - mq
  let valid := (lq - ln == a * t - (8 - a) * delta) &&
    decide (mq = mn → 0 < a → 0 < t → ln < lq) &&
    decide (0 < delta → 0 < t + delta →
      ((ln < lq ↔ 8 * delta < a * (t + delta)) ∧
       (lq = ln ↔ a * (t + delta) = 8 * delta)))
  (compare lq ln, valid)

def grid : List Int := (List.range 9).map Int.ofNat

def channelBlock (a : Int) : Nat × Nat × Nat × Bool :=
  grid.foldl (fun counts t =>
    grid.foldl (fun counts mq => grid.foldl (fun (gt, eq, lt, valid) mn =>
      let (sign, checked) := likelihoodSign a t mq mn
      (gt + (sign == .gt).toNat, eq + (sign == .eq).toNat, lt + (sign == .lt).toNat,
        valid && checked)) counts) counts) (0, 0, 0, true)

def channelCount : Nat × Nat × Nat × Bool :=
  grid.foldl (fun (gt, eq, lt, valid) a =>
    let (g, e, l, ok) := channelBlock a
    (gt + g, eq + e, lt + l, valid && ok)) (0, 0, 0, true)

set_option maxRecDepth 4096 in
theorem mixedChannels : channelCount = (4871, 305, 1385, true) ∧ 4871 + 305 + 1385 = 9^4 := by
  decide +kernel

theorem dependentChannel :
    let aq : ℚ := 3/4
    let an : ℚ := 1/4
    let t : ℚ := 1/4
    let m : ℚ := 3/4
    let lq := aq * t + (1 - aq) * m
    let ln := (1 - an) * m
    lq = 3/8 ∧ ln = 9/16 ∧ lq < ln := by
  decide +kernel

end HigherOrder

namespace Credentials

def dependency (e : Nat → Nat → Bool) (active : List Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n + 1, x, y => e x y || active.any (fun v => e x v && dependency e active n v y)

def inspect (n : Nat) (e : Nat → Nat → Bool) (active : List Nat) : Bool × Bool × Bool :=
  (active.all (fun x => active.any (e x)),
    active.all (fun x => active.any (fun y => x != y && e x y)),
    active.any (fun x => dependency e active n x x))

def countsAt (n : Nat) : Nat × Nat × Nat × Nat × Bool :=
  (masks (n*n)).foldl (fun total edgeMask => (masks n).foldl (fun (count, sn, dn, an, ok) flag =>
    let active := selected (List.range n) flag
    let e := fun x y => edgeMask.testBit (n*x+y)
    let (serial, distinct, cycle) := inspect n e active
    let inhabited := !active.isEmpty
    (count + 1, sn + (inhabited && serial).toNat, dn + (inhabited && distinct).toNat,
      an + (inhabited && !cycle).toNat,
      ok && (!(inhabited && serial) || cycle) &&
        (!(inhabited && distinct) || (cycle && serial)) &&
        (!(inhabited && !cycle) || active.any (fun x => !(active.any (e x))))))
      total) (0, 0, 0, 0, true)

def dependencyCounts : Nat × Nat × Nat × Nat × Bool :=
  [1, 2, 3].foldl (fun (n, s, d, a, valid) k =>
    let (c, sn, dn, an, ok) := countsAt k
    (n + c, s + sn, d + dn, a + an, valid && ok)) (0, 0, 0, 0, true)

set_option maxRecDepth 4096 in
theorem dependencyCensus :
    dependencyCounts = (4164, 2001, 604, 1101, true) ∧
    inspect 1 (fun x y => ([(0, 0)] : List (Nat × Nat)).contains (x, y)) [0] =
      (true, false, true) ∧
    inspect 3 (fun x y => ([(0, 1), (1, 2), (2, 1)] : List (Nat × Nat)).contains (x, y))
      [0, 1, 2] = (true, true, true) ∧
    inspect 3 (fun x y => ([(0, 1), (1, 2)] : List (Nat × Nat)).contains (x, y))
      [0, 1, 2] = (false, false, false) := by
  decide +kernel

def traceChecks (n : Nat) : Nat × Bool :=
  (masks n).foldl (fun (count, valid) flags =>
    let uses := selected (List.range n) flags
    match uses.head? with
    | none => (count, valid)
    | some first =>
      let prior := fun i => uses.any (fun j => decide (j < i))
      let earlier : List Int := (-1) :: uses.map Int.ofNat
      (count + 1, valid && !prior first && !(uses.all prior) &&
        uses.all (fun i => earlier.any (fun j => decide (j < (i : Int))))))
    (0, true)

set_option maxRecDepth 4096 in
theorem priorUse :
    (List.range 10).foldl (fun (count, valid) i =>
      let (cases, checked) := traceChecks (i + 1)
      (count + cases, valid && checked)) (0, true) = (2036, true) := by
  decide +kernel

theorem statusControls : ∀ rq bc jc rc : Bool,
    let justified := bc && jc
    let required := !rq || justified
    let grounded := !justified || rc
    (rq = true → required = true → grounded = true → rc = true) ∧
    (rq = true → bc = false → required = false) ∧
    (rq = true → justified = true → rc = false → required = true ∧ grounded = false) := by
  decide +kernel

def methodRoster : List (Bool × Bool × Bool) :=
  ((pairs bits bits).flatMap fun (q, v) => bits.map (q, v, ·)).filter fun (q, _, a) => !a || q

theorem methodInstance :
    methodRoster.length = 6 ∧
    methodRoster.any (fun (q, v, _) => q && v) ∧
    methodRoster.any (fun (q, v, _) => !q && v) ∧
    methodRoster.all (fun (q, _, a) => !a || q) ∧
    methodRoster.all (fun (q, v, a) => !(v && a) || q) ∧
    methodRoster.any (fun (_, v, a) => a && !v) ∧
    methodRoster.any (fun (_, v, a) => v && !a) := by
  decide +kernel

end Credentials

end TruthCore.Logic.ActualInquiryControls

namespace TruthCore.Logic.ActualInquiryControls.CheckValue

open TruthCore.Logic.EpistemicAccuracy.Refinement (accuracyGain)

def weight (p a b : ℚ) : ℚ := p*a + (1-p)*b
def onPositive (p a b : ℚ) : ℚ := p*a / weight p a b
def onNegative (p a b : ℚ) : ℚ := p*(1-a) / (1 - weight p a b)
def gain (w u v : ℚ) : ℚ := w * (1-w) * (u-v)^2

/-- The computable rational expression specializes the registered real
accuracy-gain theorem at rational weights and conditional credences. -/
theorem gain_agrees (w u v : ℚ) (hw : 0 ≤ w) (hw' : w ≤ 1)
    (hu : 0 ≤ u) (hu' : u ≤ 1) (hv : 0 ≤ v) (hv' : v ≤ 1) :
    (gain w u v : ℝ) = accuracyGain (w : ℝ) (u : ℝ) (v : ℝ) := by
  rw [(TruthCore.Results.Logic.EpistemicAccuracy.Refinement.checkValue
    w u v (by exact_mod_cast hw) (by exact_mod_cast hw')
    (by exact_mod_cast hu) (by exact_mod_cast hu')
    (by exact_mod_cast hv) (by exact_mod_cast hv')).1]
  simp only [gain, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_pow]

def defined (p a b : ℚ) : Bool := decide (0 < weight p a b ∧ weight p a b < 1)

def assessment (p a b : ℚ) : Bool :=
  let w := weight p a b
  let u := onPositive p a b
  let v := onNegative p a b
  let g := gain w u v
  decide (p = w*u + (1-w)*v ∧
    g = p*(1-p) - w*u*(1-u) - (1-w)*v*(1-v) ∧
    w*(1-w)*g = (p*(1-p)*(a-b))^2 ∧
    (if 0 < p ∧ p < 1 then (g = 0 ↔ a = b) else g = 0) ∧
    0 ≤ g ∧ g ≤ p*(1-p) ∧
    (if 0 < p ∧ p < 1 then (p < u ↔ b < a) else u = p) ∧
    (if 0 < p ∧ p < 1 then (v < p ↔ b < a) else v = p))

def rates : List ℚ := (List.range 13).map fun (i : ℕ) => (i : ℚ) / 12
def priors : List ℚ := (List.range 11).map fun i => (i + 1 : ℕ) / (12 : ℚ)

def countPrior (p : ℚ) : Nat × Bool :=
  rates.foldl (fun totals a => rates.foldl
    (fun (count, checked) b =>
      if defined p a b then (count + 1, checked && assessment p a b) else (count, checked))
    totals) (0, true)

def gridCount : Nat × Bool :=
  priors.foldl (fun (count, checked) p =>
    let (n, valid) := countPrior p
    (count + n, checked && valid)) (0, true)

set_option maxRecDepth 8192 in
theorem gainGrid : gridCount = (1837, true) := by
  decide +kernel

def cases : List (ℚ × ℚ × ℚ × ℚ) :=
  [(1/2, 9/10, 1/10, 4/25), (1/2, 9/1000, 1/1000, 4/4975),
    (99/100, 9/10, 1/10, 363/557500), (1/2, 7/10, 7/10, 0), (1, 9/10, 1/10, 0)]

theorem sampleGain : cases.all (fun (p, a, b, expected) => defined p a b && assessment p a b &&
    gain (weight p a b) (onPositive p a b) (onNegative p a b) == expected) := by
  decide +kernel

def factor (n : ℚ) : ℚ := (n+1)^2 / (n*(n+2))

def oddsCheck (previous n : ℚ) : ℚ × Bool :=
  let odds := previous * factor n
  (odds, decide (1 < factor n ∧ odds = 2*(n+1)/(n+2) ∧ odds < 2 ∧
    odds/(1+odds) = 2*(n+1)/(3*n+4) ∧ odds/(1+odds) < 2/3))

def oddsChecks : ℚ × Bool :=
  (List.range 1000).foldl (fun (odds, valid) i =>
    let (next, checked) := oddsCheck odds (i + 1 : ℕ)
    (next, valid && checked)) (1, true)

set_option maxRecDepth 4096 in
theorem boundedUpdates : oddsChecks.2 = true := by
  decide +kernel

end TruthCore.Logic.ActualInquiryControls.CheckValue
