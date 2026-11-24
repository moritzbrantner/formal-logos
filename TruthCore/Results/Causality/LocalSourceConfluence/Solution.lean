module

public import TruthCore.Causality.LocalSourceConfluence
public import TruthCore.Causality.ActualRootUniqueness
public import TruthCore.Results.Causality.SourceForest.Solution

@[expose] public section

namespace TruthCore.Results.Causality.LocalSourceConfluence
open TruthCore.Logic.Regress
open TruthCore.Causality.SourceForest
open TruthCore.Causality.LocalSourceConfluence
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Causality.ConcreteExistentialSupply (graph)
open TruthCore.Causality.RootPositiveIntellectWill (ActualRootExistsAt)
open TruthCore.Causality.ActualRootUniqueness (UniqueActualRootAt)

theorem confluenceOfLocalForks {N : Type} (G : Graph N)
    (hWF : WellFoundedEdges G) (hFork : LocalForksJoin G) : UpstreamConfluent G := by
  intro x
  induction x using hWF.induction with
  | h x ih =>
    intro b c hxb hxc
    obtain rfl | ⟨u, hux, hub⟩ := hxb.cases_head
    · exact ⟨c, hxc, .refl⟩
    obtain rfl | ⟨v, hvx, hvc⟩ := hxc.cases_head
    · exact ⟨b, .refl, .head hux hub⟩
    obtain ⟨k, huk, hvk⟩ := hFork x u v hux hvx
    obtain ⟨p, hbp, hkp⟩ := ih u hux b k hub huk
    obtain ⟨t, hct, hpt⟩ := ih v hvx c p hvc (hvk.trans hkp)
    exact ⟨t, hbp.trans hpt, hct⟩

theorem obstructionOfTwoSources {N : Type} (G : Graph N)
    (hWF : WellFoundedEdges G) (hConnected : WeaklyConnected G)
    (a b : N) (ha : G.Source a) (hb : G.Source b) (hne : a ≠ b) :
    ∃ x y z, G.edge y x ∧ G.edge z x ∧
      ¬ Relation.Join (Relation.ReflTransGen (fun u v => G.edge v u)) y z := by
  classical
  by_contra missing
  apply hne
  apply SourceForest.sources_eq_of_connected_pair G _ a b (hConnected a b) ha hb
  apply confluenceOfLocalForks G hWF
  intro x y z hy hz
  by_contra unjoinable
  exact missing ⟨x, y, z, hy, hz, unjoinable⟩

theorem uniqueActualOfSourceAgreement {W B : Type} (m : Profile W B) (w : W)
    (hRoot : ActualRootExistsAt m w) (hAgreement : AtMostOneSource (graph m w)) :
    UniqueActualRootAt m w := by
  obtain ⟨s, hs⟩ := hRoot
  refine ⟨s, hs, fun x hx => ?_⟩
  have source (b : B) (hb : TruthCore.Causality.NecessaryRootFork.ActualRoot m w b) :
      (graph m w).Source ⟨b, hb.1⟩ := by
    rintro ⟨c, hc⟩
    exact hb.2 c.val ⟨c.property.1, c.property.2, hc⟩
  exact congrArg Subtype.val (hAgreement _ _ (source x hx) (source s hs))

theorem uniqueActualOfLocalForks {W B : Type} (m : Profile W B) (w : W)
    (hRoot : ActualRootExistsAt m w) (hWF : ActualGroundingWF m w)
    (hConnected : WeaklyConnected (graph m w)) (hFork : LocalForksJoin (graph m w)) :
    UniqueActualRootAt m w := by
  exact uniqueActualOfSourceAgreement m w hRoot
    (SourceForest.atMostOne_of_confluent (graph m w) hConnected
      (confluenceOfLocalForks (graph m w) hWF hFork))

theorem alternatingSources : LadderControl := by
  have root (b : Bool) : ladder.Source (.root b) := by
    rintro ⟨y, hy⟩
    cases hy
  have toZero (x : LadderNode) : Relation.EqvGen Feeds x (.stage 0) := by
    have stages (n : Nat) : Relation.EqvGen Feeds (.stage n) (.stage 0) := by
      induction n with
      | zero => exact .refl _
      | succ n ih => exact .trans _ _ _ (.rel _ _ (.relay n)) ih
    cases x with
    | stage n => exact stages n
    | root b =>
      cases b
      · exact .rel _ _ (.origin 0)
      · exact .trans _ _ _ (.rel _ _ (.origin 1)) (stages 1)
  have connected : WeaklyConnected ladder := fun a b =>
    .trans _ _ _ (toZero a) (.symm _ _ (toZero b))
  have forks : LocalForksJoin ladder := by
    have back (n : Nat) : Relation.ReflTransGen (fun a b => Feeds b a)
        (.stage (n + 1)) (.root (side n)) := by
      have hSide : side (n + 2) = side n := Bool.not_not _
      exact .head (.relay (n + 1)) (.single (hSide ▸ Feeds.origin (n + 2)))
    intro x y z hy hz
    cases hy with
    | relay n =>
      cases hz with
      | relay => exact ⟨_, .refl, .refl⟩
      | origin => exact ⟨_, back n, .refl⟩
    | origin n =>
      cases hz with
      | relay => exact ⟨_, .refl, back n⟩
      | origin => exact ⟨_, .refl, .refl⟩
  have notConfluent : ¬ UpstreamConfluent ladder := by
    intro h
    have eq := SourceForest.atMostOne_of_confluent ladder connected h _ _ (root false) (root true)
    cases eq
  refine ⟨connected, ?_, forks, ?_, root false, root true, by decide, notConfluent,
    fun wf => notConfluent (confluenceOfLocalForks ladder wf forks)⟩
  · let ahead : LadderNode → LadderNode → Prop
          | .stage m, .stage n => n < m
          | .root _, .stage _ => True
          | _, .root _ => False
    have step {x y : LadderNode} (h : Feeds x y) : ahead x y := by
      cases h with
      | relay n => exact Nat.lt_succ_self n
      | origin => exact True.intro
    have trans {x y z : LadderNode} (a : ahead x y) (b : ahead y z) : ahead x z := by
      cases x <;> cases y <;> cases z <;> first
        | exact False.elim a
        | exact False.elim b
        | exact True.intro
        | exact Nat.lt_trans b a
    intro x path
    have forward {a b : LadderNode} (p : Relation.TransGen ladder.edge a b) : ahead a b := by
      induction p with
      | single h => exact step h
      | tail _ h ih => exact trans ih (step h)
    have impossible := forward path
    cases x with
    | stage n => exact Nat.lt_irrefl n impossible
    | root => exact impossible
  · intro x
    cases x with
    | root b => exact ⟨_, root b, Or.inl rfl⟩
    | stage n => exact ⟨_, root (side n), Or.inr (.origin n)⟩

end TruthCore.Results.Causality.LocalSourceConfluence
