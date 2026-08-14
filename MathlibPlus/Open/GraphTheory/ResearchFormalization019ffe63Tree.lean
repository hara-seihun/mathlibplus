import Mathlib

namespace MathlibPlus.Open.GraphTheory

noncomputable section

/-- A leaf in a finite labelled presentation of a tree. -/
def treeLeaf {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  T.degree v = 1

def leafDeletedGraph {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph {x : Fin n // x ≠ v} :=
  T.induce {x : Fin n | x ≠ v}

/-- Claim 5513: isomorphic leaf-deleted cards of a finite tree come from an
automorphism taking one deleted leaf to the other. -/
def removalSimilarLeavesAreAutomorphic_claim5513 : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (ℓ ℓ' : Fin n),
    T.IsTree →
      treeLeaf T ℓ → treeLeaf T ℓ' →
        Nonempty (SimpleGraph.Iso (leafDeletedGraph T ℓ)
          (leafDeletedGraph T ℓ')) →
          ∃ e : SimpleGraph.Iso T T, e ℓ = ℓ'

end

end MathlibPlus.Open.GraphTheory
