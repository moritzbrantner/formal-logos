module

public import TruthCore.Causality.SustainingDependence

/-!
# Present-tense receipt of esse and the correlativity of receiving and giving

Analyst formulations, attribution deferred. Research note:
`docs/notes/sustaining-vs-existential-inertia.md`, section 5.

The sustaining-versus-inertia comparison (attempt `21883b61`) found no
discriminating test at the crux, weak concurrent actualization `40a97664`
(`ConcurrentlyActualized`): whatever has its esse received in some principle is
given being by something at every moment at which it is present. Its named next
test: type a present-tense receipt and a principle that receiving and giving go
together, and see whether the dispute moves to the tense of the reception
bridge `da72ae93` (`CausedEsseIsReceived`).

**Present-tense receipt** (`Receipt.ReceivesAt v z x t`, explicitly
PRIMITIVE). In history `v`, at moment `t`, the principle `z` is receiving the
act of being of `x`: `z` stands to `x`'s esse as receiving potency to received
act *at* `t`. It is the time-indexed counterpart of the tenseless
`EsseReceivedIn x z` (DEF-ESSE-RECEIVED-IN). It names the receiver side only;
no giver occurs in it, and no axiom ties it to `GivesAt`. Two defined
interpretations are recorded below as its senses (`passionReceipt`,
`standingReceipt`); the theorems over the primitive hold for every
interpretation.

**Present-tense reading of reception** (`ReceptionIsPresent`, open). In every
history, whatever has its esse received in `z` is, at every moment at which it
is present, receiving its esse in `z` then: "x has esse as received, at each t".

**Onset reading of reception** (`ReceptionAtOnset`, open). In every history,
whatever has its esse received in `z` received it in `z` at a first moment of
its presence: "x received esse at onset". It is entailed by the present-tense
reading and says nothing about later moments, so it is the part of the
past-tense reading that both sides grant; the past-tense reading proper is this
together with the denial of the present-tense reading at later moments.

**Correlativity** (`ReceivingIsCorrelativeWithGiving`, open). In every history,
whatever is receiving its esse at `t` is given being at `t` by something
(`GivesAt`, STRICT esse-giving reading, definition `158301bc`).

Results: present-tense reading + correlativity ⊢ `40a97664`; onset reading +
correlativity ⊢ received onset is given `fa3e228b`, which the inertialist
grants. The two senses: on `passionReceipt` (the tenseless reception
conjoined with some giving of being to `x` at `t`; that the giving is the
agent side of the receiving in `z` is the intended reading, not typed)
correlativity holds by definition and the present-tense reading is equivalent
to `40a97664`; on `standingReceipt` (the tenseless reception conjoined with
presence at `t`) the present-tense reading holds by definition and
correlativity is equivalent to `40a97664`. With the receipt interpretation
quantified existentially, the pair is equivalent to `40a97664`
(`SomeReceiptCarriesTheCrux`); the strict separation in `Control` part 3 holds
only for a fixed interpretation.

Applicability of every premise below to reality remains OPEN.
-/

@[expose] public section

namespace TruthCore.Causality.PresentReceipt

open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.SustainingCausation
open TruthCore.Causality.ConcurrentActualization

/-- Present-tense receipt of esse, an explicitly primitive relation:
`ReceivesAt v z x t` says that in history `v`, at moment `t`, the principle `z`
is receiving the act of being of `x`. -/
structure Receipt (W B T P : Type) where
  ReceivesAt : W → P → B → T → Prop

/-- Present-tense reading of reception: in every history, whatever has its esse
received in `z` is receiving it in `z` at every moment at which it is present. -/
def ReceptionIsPresent {W B T P : Type} (h : History W B T) (R : Receipt W B T P)
    (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x z t, EsseReceivedIn x z → h.IsAt v x t → R.ReceivesAt v z x t

/-- Onset reading of reception: in every history, whatever has its esse received
in `z` is receiving it in `z` at a first moment of its presence. -/
def ReceptionAtOnset {W B T P : Type} [Preorder T] (h : History W B T)
    (R : Receipt W B T P) (EsseReceivedIn : B → P → Prop) : Prop :=
  ∀ v x z b, EsseReceivedIn x z → BeginsAt h v x b → R.ReceivesAt v z x b

/-- Correlativity of receiving and giving: in every history, whatever is
receiving its esse at `t` is given being at `t` by something. -/
def ReceivingIsCorrelativeWithGiving {W B T P : Type} (G : BeingGiving W B T)
    (R : Receipt W B T P) : Prop :=
  ∀ v z x t, R.ReceivesAt v z x t → ∃ g, G.GivesAt v g x t

/-- RECEIVES_ESSE_AT_1, receipt as passion: `z` receives `x`'s esse at `t` iff
`x`'s esse is received in `z` and something gives `x` being at `t`. A bare
conjunction: nothing ties the giving to `z`. -/
def passionReceipt {W B T P : Type} (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop) : Receipt W B T P :=
  ⟨fun v z x t => EsseReceivedIn x z ∧ ∃ g, G.GivesAt v g x t⟩

/-- RECEIVES_ESSE_AT_2, receipt as standing composition: `z` receives `x`'s esse
at `t` iff `x`'s esse is received in `z` and `x` is present at `t`. -/
def standingReceipt {W B T P : Type} (h : History W B T)
    (EsseReceivedIn : B → P → Prop) : Receipt W B T P :=
  ⟨fun v z x t => EsseReceivedIn x z ∧ h.IsAt v x t⟩

/-- On the passion sense, correlativity holds and the present-tense reading is
equivalent to weak concurrent actualization, for every history, giving relation
and reception predicate. -/
def PassionReadingIsTheCrux : Prop :=
  ∀ (W B T P : Type) (h : History W B T) (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop),
    ReceivingIsCorrelativeWithGiving G (passionReceipt G EsseReceivedIn) ∧
    (ReceptionIsPresent h (passionReceipt G EsseReceivedIn) EsseReceivedIn ↔
      ConcurrentlyActualized h G EsseReceivedIn)

/-- On the standing sense, the present-tense reading holds and correlativity is
equivalent to weak concurrent actualization, for every history, giving relation
and reception predicate. -/
def StandingReadingIsTheCrux : Prop :=
  ∀ (W B T P : Type) (h : History W B T) (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop),
    ReceptionIsPresent h (standingReceipt h EsseReceivedIn) EsseReceivedIn ∧
    (ReceivingIsCorrelativeWithGiving G (standingReceipt h EsseReceivedIn) ↔
      ConcurrentlyActualized h G EsseReceivedIn)

/-- Some receipt interpretation satisfies the present-tense reading and
correlativity iff weak concurrent actualization holds, for every history,
giving relation and reception predicate. -/
def SomeReceiptCarriesTheCrux : Prop :=
  ∀ (W B T P : Type) (h : History W B T) (G : BeingGiving W B T)
    (EsseReceivedIn : B → P → Prop),
    (∃ R : Receipt W B T P, ReceptionIsPresent h R EsseReceivedIn ∧
      ReceivingIsCorrelativeWithGiving G R) ↔
    ConcurrentlyActualized h G EsseReceivedIn

namespace Control

open TruthCore.Causality.SustainingCausation.Control
open TruthCore.Causality.ConcurrentActualization.Control
open TruthCore.Causality.SustainingDependence (ReceivedOnsetIsGiven)

/-- Receipt at the first moment only: `false` receives its esse at time `1`. -/
def onsetReceipt : Receipt Unit Bool Nat Unit := ⟨fun _ _ x t => x = false ∧ t = 1⟩

/-- No receipt. -/
def noReceipt : Receipt Unit Bool Nat Unit := ⟨fun _ _ _ _ => False⟩

/-- Omission, rival-reading, separation and nonvacuity controls, one world,
natural-number times, `false` alone with received esse; histories from
`SustainingCausation.Control`.
(1) Inertia, past-tense receipt (`inertia`, giving at time `1` only, receipt
at time `1` only): the onset reading and correlativity hold; the present-tense
reading and `40a97664` fail; received onset is given.
(2) Inertia, standing receipt: the present-tense and onset readings hold;
correlativity and `40a97664` fail.
(3) Sustaining with no receipt (`sustained`, its giving): `40a97664` holds;
the present-tense and onset readings fail; correlativity holds.
(4) Inertia with no giving and no receipt: correlativity holds; the onset
reading and received onset fail.
(5) Inertia with no giving, standing receipt: the onset reading holds;
correlativity and received onset fail.
(6) Sustaining, standing receipt: every premise and `40a97664` hold. -/
def Certificate : Prop :=
  (ReceptionAtOnset inertia onsetReceipt falseReceived ∧
    ReceivingIsCorrelativeWithGiving inertiaGiving onsetReceipt ∧
    ¬ ReceptionIsPresent inertia onsetReceipt falseReceived ∧
    ¬ ConcurrentlyActualized inertia inertiaGiving falseReceived ∧
    ReceivedOnsetIsGiven inertia inertiaGiving falseReceived) ∧
  (ReceptionIsPresent inertia (standingReceipt inertia falseReceived) falseReceived ∧
    ReceptionAtOnset inertia (standingReceipt inertia falseReceived) falseReceived ∧
    ¬ ReceivingIsCorrelativeWithGiving inertiaGiving (standingReceipt inertia falseReceived) ∧
    ¬ ConcurrentlyActualized inertia inertiaGiving falseReceived) ∧
  (ConcurrentlyActualized sustained sustainedGiving falseReceived ∧
    ¬ ReceptionIsPresent sustained noReceipt falseReceived ∧
    ¬ ReceptionAtOnset sustained noReceipt falseReceived ∧
    ReceivingIsCorrelativeWithGiving sustainedGiving noReceipt) ∧
  (ReceivingIsCorrelativeWithGiving noGiving noReceipt ∧
    ¬ ReceptionAtOnset inertia noReceipt falseReceived ∧
    ¬ ReceivedOnsetIsGiven inertia noGiving falseReceived) ∧
  (ReceptionAtOnset inertia (standingReceipt inertia falseReceived) falseReceived ∧
    ¬ ReceivingIsCorrelativeWithGiving noGiving (standingReceipt inertia falseReceived) ∧
    ¬ ReceivedOnsetIsGiven inertia noGiving falseReceived) ∧
  (ReceptionIsPresent sustained (standingReceipt sustained falseReceived) falseReceived ∧
    ReceptionAtOnset sustained (standingReceipt sustained falseReceived) falseReceived ∧
    ReceivingIsCorrelativeWithGiving sustainedGiving (standingReceipt sustained falseReceived) ∧
    ConcurrentlyActualized sustained sustainedGiving falseReceived)

end Control

end TruthCore.Causality.PresentReceipt
