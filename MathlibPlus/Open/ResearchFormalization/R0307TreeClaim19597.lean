import Mathlib
import MathlibPlus.Open.Combinatorics.TreeOperators

namespace MathlibPlus.Open.ResearchFormalization.R0307

open MathlibPlus.Open.Combinatorics

/-- Claim 19597: on the positive tree levels, leaf deletion and pendant
    grafting have commutator `n` times the identity, with the concrete
    shifted indexing displayed in the source. -/
def treeLeafGraftCommutator_claim19597 : Prop :=
  (∀ (n : ℕ), 1 ≤ n →
    ∀ x : GraphSpace (n + 1), x ∈ treeSpace (n + 1) →
      L (n + 1) (G (n + 1) x) - G n (L n x) =
        (n + 1 : ℚ) • x) ∧
    (∀ (n : ℕ) (x : GraphSpace (n + 2)), x ∈ treeSpace (n + 2) →
      L (n + 2) (G (n + 2) x) =
        (n + 2 : ℚ) • x + G (n + 1) (L (n + 1) x))

end MathlibPlus.Open.ResearchFormalization.R0307
