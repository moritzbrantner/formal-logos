module

public import TruthCore.Causality.DeiFiliusLordBlessed
public import TruthCore.Causality.DeiFiliusUnifiedRoute
public import TruthCore.Case.Catholicism.DivineLoveBridge
public import TruthCore.Case.Catholicism.DivineLoveSenses

/-!
LORD_3, a third typed sibling of the Dei Filius lord primitive (#1733).

The registered sense bridge `CauseAndGovernorOfAllIsLord` (LORD_2 → LORD_1)
passes from causing the being of everything else and governing everything else
to dominion, i.e. authority to dispose. The moral-authority investigation
(`docs/notes/natural-goodness-function-and-authority.md`, #1508/#1460) records
the Cudworth/Wielenberg-style objection that creation or power alone does not
license authority, and the natural-law reply that authority is tied to wise care
for the good of those governed. LORD_3 adds to LORD_2 one typed conjunct of that
reply: the being wills some good of their own to every other intellectual being
in act as to being (`WillsGoodFor`, recipient-directed willing, CREATURE_WILLING_1).
The authority step remains an OPEN sense bridge, `BenevolentCauseAndGovernorOfAllIsLord`;
it is strictly weaker than the LORD_2 bridge (`Control.Controls` part 2).

The willing premise `IntellectualRecipientExistenceWilling` is restricted to
intellectual recipients. It follows from the #1732 result
`DivineWillsGoodForAllExisting` alone, and from `CausalExistenceWilling` with the
q.5 a.1 coextension; it is consistent with the strong (exclusive) ordered-love
variant `OrderedExistenceWilling` (1dd68893, an unattributed analyst strengthening
of q.20 a.2 ad 3) on a non-rational effect where `CausalExistenceWilling` fails
(`Control.Controls` part 5). That conflict holds for the strong variant only; the
weak, ad-3-faithful ordered reading is compatible with `CausalExistenceWilling`.

What is NOT typed: that God governs each intellectual being *for* the good willed
to it (the governance and willing conjuncts are separate, as LORD_2's two
conjuncts are); wisdom beyond having intellect; justice; and the directed moral
jurisdiction to impose obligations on rational creatures. LORD_1 is dominion
over everything else, not a typed account of moral obligation; the passage from
dominion to directed obligation is a separate unbuilt transition.

Analyst formulations, attribution deferred: no source claim states any of them.
-/

@[expose] public section

namespace TruthCore.Causality.DeiFiliusBenevolentLord

open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.DeiFiliusLordBlessed

/-- g wills some good of its own to every other intellectual being in act as to
being: for each such x there is a respect r in which x is good and g wills that
good to x (`WillsGoodFor g x r`, recipient-directed willing). The respect is
existential; nothing is said about every good of x or about non-intellectual
beings. -/
def WillsGoodToIntellectualOthers {Being Respect : Type}
    (InAct GoodIn : Being → Respect → Prop) (HasIntellect : Being → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect) (g : Being) : Prop :=
  ∀ x, x ≠ g → InAct x esse → HasIntellect x → ∃ r, GoodIn x r ∧ WillsGoodFor g x r

/-- LORD_3: LORD_2 (g causes the being of and governs every other being in act as
to being) and g wills some good of their own to every other intellectual being in
act as to being. The two conjuncts are separate: the type does not say that the
governance is directed to the good willed. -/
def IsBenevolentLordByCauseAndGovernment {Being Respect : Type}
    (InAct GoodIn : Being → Respect → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (Governs : Being → Being → Prop) (HasIntellect : Being → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (g : Being) : Prop :=
  IsLordByCauseAndGovernment InAct CausesIn esse Governs g ∧
    WillsGoodToIntellectualOthers InAct GoodIn HasIntellect WillsGoodFor esse g

/-- OPEN application bridge, restricted to intellectual recipients: for every
GOD_4 g with will and every distinct intellectual x in act as to being whose being
g causes, g wills x some good of x. Weaker than `DivineWillsGoodForAllExisting`
(it restricts to distinct intellectual recipients and adds the HasWill and
CausesIn antecedents) and, with the q.5 a.1 coextension, than
`CausalExistenceWilling`. -/
def IntellectualRecipientExistenceWilling {Being Respect : Type}
    (IsGod HasWill HasIntellect : Being → Prop) (InAct GoodIn : Being → Respect → Prop)
    (CausesIn : Being → Being → Respect → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∀ g x, IsGod g → HasWill g → x ≠ g → InAct x esse → HasIntellect x →
    CausesIn g x esse → ∃ r, GoodIn x r ∧ WillsGoodFor g x r

/-- OPEN sense bridge LORD_3 → LORD_1: whatever causes the being of everything
else, governs everything else and wills some good of their own to every other
intellectual being has dominion over everything else. It carries what LORD_3
leaves untyped: the passage from causal, directive and benevolent volitional
relations to authority. Strictly weaker than `CauseAndGovernorOfAllIsLord`
(its antecedent adds the willing conjunct; `Control.Controls` part 2). -/
def BenevolentCauseAndGovernorOfAllIsLord {Being Respect : Type}
    (InAct GoodIn : Being → Respect → Prop) (CausesIn : Being → Being → Respect → Prop)
    (esse : Respect) (Governs : Being → Being → Prop) (HasIntellect : Being → Prop)
    (WillsGoodFor : Being → Being → Respect → Prop) (D : Primitives Being) : Prop :=
  ∀ g, IsBenevolentLordByCauseAndGovernment InAct GoodIn CausesIn esse Governs HasIntellect
    WillsGoodFor g → D.IsLord g

/-! ## Controls -/

namespace Control

open TruthCore.Case.Catholicism.DivineLoveBridge
open TruthCore.Case.Catholicism.DivineLoveSenses

/-- Two beings: `true` is GOD_4; `false` is the other being. -/
def isGod (b : Bool) : Prop := b = true
def everywhere (_ : Bool) (_ : Unit) : Prop := True
def all (_ : Bool) : Prop := True
def causes (g x : Bool) (_ : Unit) : Prop := g = true ∧ x = false
def governs (g x : Bool) : Prop := g = true ∧ x = false
/-- Recipient willing: `true` wills good to `false`, or nothing is willed. -/
def wills (on : Bool) (g x : Bool) (_ : Unit) : Prop := on = true ∧ g = true ∧ x = false
/-- Lord primitive: only `true`, or nothing. -/
def lordPrims (on : Bool) : Primitives Bool :=
  ⟨all, fun b => on = true ∧ b = true, all, all, all⟩
/-- In the second interpretation only `true` has intellect. -/
def onlyTrue (b : Bool) : Prop := b = true
/-- Ordered willing: `true` wills `false`'s being as ordered to itself. -/
def ordered : OrderedWilling Bool Unit := ⟨fun g x y _ => g = true ∧ x = false ∧ y = true⟩

/-- The controls, statements about these interpretations only:
(1) nonvacuity: with willing and lordship, the restricted willing premise and the
LORD_3 bridge hold and `true` is LORD_3 and LORD_1;
(2) strictness of the bridge: without willing and with nothing LORD_1, the LORD_3
bridge holds and the LORD_2 bridge fails;
(3) sense mixing: with willing and nothing LORD_1, `true` is LORD_3 and not LORD_1;
(4) necessity of willing: without willing, `true` is LORD_2 and not LORD_3, the
other being having intellect;
(5) strictness and compatibility of the restricted willing premise: when only
`true` has intellect and nothing is willed, the restricted premise, the q.5 a.1
coextension and the strong (exclusive) ordered-love variant (rational = has intellect)
hold, while `DivineWillsGoodForAllExisting` and `CausalExistenceWilling` fail. -/
def Controls : Prop :=
  (IntellectualRecipientExistenceWilling isGod all all everywhere everywhere causes (wills true) () ∧
    BenevolentCauseAndGovernorOfAllIsLord everywhere everywhere causes () governs all (wills true)
      (lordPrims true) ∧
    IsBenevolentLordByCauseAndGovernment everywhere everywhere causes () governs all (wills true)
      true ∧
    (lordPrims true).IsLord true) ∧
  (BenevolentCauseAndGovernorOfAllIsLord everywhere everywhere causes () governs all (wills false)
      (lordPrims false) ∧
    ¬ CauseAndGovernorOfAllIsLord everywhere causes () governs (lordPrims false)) ∧
  (IsBenevolentLordByCauseAndGovernment everywhere everywhere causes () governs all (wills true)
      true ∧
    ¬ (lordPrims false).IsLord true) ∧
  (IsLordByCauseAndGovernment everywhere causes () governs true ∧
    ¬ IsBenevolentLordByCauseAndGovernment everywhere everywhere causes () governs all
      (wills false) true) ∧
  (IntellectualRecipientExistenceWilling isGod all onlyTrue everywhere everywhere causes
      (wills false) () ∧
    TruthCore.Latin.Aquinas.SummaTheologiae.GoodnessIsActualityReading everywhere everywhere ∧
    OrderedExistenceWilling isGod all onlyTrue everywhere causes ⟨wills false⟩ ordered () ∧
    ¬ DivineWillsGoodForAllExisting isGod everywhere everywhere (wills false) () ∧
    ¬ CausalExistenceWilling isGod all everywhere causes (wills false) ())

section RootModel

open TruthCore.Case.Catholicism
open TruthCore.Causality.DeiFiliusUnifiedRoute.Control
open TruthCore.Causality.RootPositiveIntellectWillControl
  (model prior component matterForm intellect will)
open TruthCore.Causality.NecessaryClassicalGodRootControl (signature eternal)

/-- Recipient willing in the unified root model: every being wills every good to
every being (a permissive assignment, used only to witness satisfiability). -/
def rootWills (_ _ : TransferRole) (_ : Bool) : Prop := True

/-- Joint-satisfiability model of the LORD_3 root route, on the unified route's
root model (four roles; `source` the root, `recipient` a second intellectual
being): given excluded middle, the unified root bundle holds (it contains every
premise of the LORD_3 route except the two new ones, and also the LORD_2 bridge
that the new route omits), the restricted willing premise and the LORD_3 bridge
hold, `recipient` is an intellectual being other than `source`, and the selected
root has every Dei Filius attribute. Statements about this interpretation only;
its willing relation is permissive, so it does not discriminate recipient-directed
from other willing. -/
def RootModel : Prop :=
  TruthCore.Logic.ExcludedMiddle →
    RootBundle ∧
    IntellectualRecipientExistenceWilling signature.IsGod will intellect rootProfile.InAct
      transferAct rootProfile.CausesIn rootWills rootProfile.esse ∧
    BenevolentCauseAndGovernorOfAllIsLord rootProfile.InAct transferAct rootProfile.CausesIn
      rootProfile.esse rootGoverns intellect rootWills rootPrims ∧
    (TransferRole.recipient ≠ TransferRole.source ∧ intellect TransferRole.recipient) ∧
    TruthCore.Causality.DeiFiliusAttributeField.NecessaryDeiFiliusGodRootAt signature model false
      rootProfile transferAct rootPotency (transferMore true) prior component rootComposite
      matterForm rootInfinite eternal intellect will rootPower rootPrims

end RootModel

end Control

end TruthCore.Causality.DeiFiliusBenevolentLord
