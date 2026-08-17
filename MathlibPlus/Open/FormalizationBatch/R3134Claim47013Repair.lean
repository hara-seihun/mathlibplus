import Mathlib
import MathlibPlus.Open.FormalizationBatch.TreeCover

namespace MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open Set

/-- The dual graph has one vertex for each cover member and joins two members
when they share a vertex of the support tree. -/
def dualIncidenceGraph {V A : Type}
    (C : A → Set V) : SimpleGraph A :=
  SimpleGraph.fromRel (fun a b => ∃ v : V, v ∈ C a ∧ v ∈ C b)

/-- A source vertex is sent to the dual edge determined by its two cover
members.  The membership clauses make this an incidence map, not an arbitrary
bijection with the edge set. -/
def incidenceMap {V A : Type} [Fintype V] [Fintype A]
    (C : A → Set V) (H : SimpleGraph A)
    (β : V ≃ H.edgeSet) : Prop :=
  ∀ v : V, ∃ a b : A,
    a ≠ b ∧ v ∈ C a ∧ v ∈ C b ∧
      (β v : Sym2 A) = Sym2.mk a b

/-- A line-tree envelope is the displayed tree H on one more vertex together
with the edge bijection whose image respects adjacency in the line graph. -/
def lineTreeEnvelopeWithMap {V A : Type} [Fintype V] [Fintype A]
    (T : SimpleGraph V) (H : SimpleGraph A)
    (β : V ≃ H.edgeSet) : Prop :=
  T.IsTree ∧ H.IsTree ∧
    Fintype.card A = Fintype.card V + 1 ∧
      ∀ u v : V, T.Adj u v → H.lineGraph.Adj (β u) (β v)

def lineTreeEnvelope {V A : Type} [Fintype V] [Fintype A]
    (T : SimpleGraph V) (H : SimpleGraph A) : Prop :=
  ∃ β : V ≃ H.edgeSet, lineTreeEnvelopeWithMap T H β

/-- The exact converse/presentation carrier: a line-tree envelope is required
also to use the dual incidence edges of the given cover. -/
def coverEnvelopePresentation {V A : Type} [Fintype V] [Fintype A]
    (T : SimpleGraph V) (C : A → Set V) : Prop :=
  ∃ H : SimpleGraph A, ∃ β : V ≃ H.edgeSet,
    H = dualIncidenceGraph C ∧
      lineTreeEnvelopeWithMap T H β ∧ incidenceMap C H β

/-- Claim 47013: an exact connected 2-cover has the stated counts and dual
incidence tree, and the cover/envelope correspondence is an equivalence rather
than only a one-way dual-tree construction. -/
def claim47013 : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
    (T : SimpleGraph V) (C : A → Set V),
    T.IsTree →
      (MathlibPlus.Open.FormalizationBatch.TreeCover.exactConnected2Cover T C →
        Fintype.card A = Fintype.card V + 1 ∧
          (∑ a : A, (Set.ncard (C a) : ℤ)) = 2 * (Fintype.card V : ℤ) ∧
            (∑ a : A, (Set.ncard (C a) : ℤ) - 1) =
              (Fintype.card V : ℤ) - 1 ∧
                MathlibPlus.Open.FormalizationBatch.TreeCover.pairwiseIntersectsAtMostOne C ∧
                  (dualIncidenceGraph C).Connected ∧
                    Fintype.card (dualIncidenceGraph C).edgeSet = Fintype.card V ∧
                      (dualIncidenceGraph C).IsTree ∧
                      lineTreeEnvelope T (dualIncidenceGraph C) ∧
                        ∃ β : V ≃ (dualIncidenceGraph C).edgeSet,
                          incidenceMap C (dualIncidenceGraph C) β ∧
                            lineTreeEnvelopeWithMap
                              T (dualIncidenceGraph C) β) ∧
        (MathlibPlus.Open.FormalizationBatch.TreeCover.exactConnected2Cover T C ↔
          coverEnvelopePresentation T C)

end

end MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair
