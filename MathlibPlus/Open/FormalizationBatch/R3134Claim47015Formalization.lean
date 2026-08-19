import Mathlib
import MathlibPlus.Open.FormalizationBatch.Graphs
import MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair

namespace MathlibPlus.Open.FormalizationBatch.R3134Claim47015Formalization

noncomputable section
open Classical

/-- A line-tree envelope attaining the minimum rooted sequence over all
finite-carrier line-tree envelopes of the same source tree. -/
def minimalLineTreeEnvelope {V A : Type} [Fintype V] [Fintype A]
    (T : SimpleGraph V) (H : SimpleGraph A) : Prop :=
  MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair.lineTreeEnvelope T H ∧
    ∀ {K : Type} [Fintype K] (G : SimpleGraph K),
      MathlibPlus.Open.FormalizationBatch.R3134Claim47013Repair.lineTreeEnvelope T G →
        MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair.minimumRootedSequence H ≤
          MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair.minimumRootedSequence G

/-- A finite envelope carrier is a path when it is graph-isomorphic to the
standard path on its cardinality. -/
def pathEnvelope {A : Type} [Fintype A] (H : SimpleGraph A) : Prop :=
  Nonempty (H ≃g SimpleGraph.pathGraph (Fintype.card A))

/-- Claim 47015: minimal line-tree envelopes are nonempty, their minimum-leaf
vertex deletions recover the source tree, and the selected envelope is a
complete invariant (with the path special case). -/
def claim47015 : Prop :=
  ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
    T.IsTree →
      (∃ (A : Type) (_ : Fintype A) (H : SimpleGraph A),
        minimalLineTreeEnvelope T H) ∧
      (∀ {A : Type} [Fintype A] (H : SimpleGraph A),
        minimalLineTreeEnvelope T H →
        ∀ ℓ : A,
          MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair.minimumLeaf H ℓ →
          Nonempty
            (MathlibPlus.Open.FormalizationBatch.Graphs.deletedGraph H ℓ ≃g T)) ∧
      (∀ {V' : Type} [Fintype V'] (T' : SimpleGraph V'),
        T'.IsTree →
        ∀ {A₁ A₂ : Type} [Fintype A₁] [Fintype A₂]
          (H₁ : SimpleGraph A₁) (H₂ : SimpleGraph A₂),
          minimalLineTreeEnvelope T H₁ →
          minimalLineTreeEnvelope T' H₂ →
          Nonempty (H₁ ≃g H₂) →
          (∀ (ℓ₁ : A₁) (ℓ₂ : A₂),
            MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair.minimumLeaf H₁ ℓ₁ →
            MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair.minimumLeaf H₂ ℓ₂ →
            Nonempty
              (MathlibPlus.Open.FormalizationBatch.Graphs.deletedGraph H₁ ℓ₁ ≃g
                MathlibPlus.Open.FormalizationBatch.Graphs.deletedGraph H₂ ℓ₂)) ∧
            Nonempty (T ≃g T')) ∧
      (∀ {A : Type} [Fintype A] (H : SimpleGraph A),
        minimalLineTreeEnvelope T H →
        pathEnvelope H →
        ∀ ℓ₁ ℓ₂ : A,
          MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair.minimumLeaf H ℓ₁ →
          MathlibPlus.Open.FormalizationBatch.R3134Claim47016Repair.minimumLeaf H ℓ₂ →
          Nonempty
            (MathlibPlus.Open.FormalizationBatch.Graphs.deletedGraph H ℓ₁ ≃g
              MathlibPlus.Open.FormalizationBatch.Graphs.deletedGraph H ℓ₂))

end

end MathlibPlus.Open.FormalizationBatch.R3134Claim47015Formalization
