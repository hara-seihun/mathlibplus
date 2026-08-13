import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- For every prime `p ≥ 5`, the direct product `C_p × A₄` has an explicit
valency-six directed Cayley-isomorphism defect. -/
def alternatingFourCyclicPrimeDirectedCIDefect : Prop :=
  ∀ p : ℕ, Nat.Prime p → 5 ≤ p →
    let G := Multiplicative (ZMod p) × alternatingGroup (Fin 4)
    ∃ (S T : Set G) (q : G ≃ G),
      q 1 = 1 ∧
      q.symm = q ∧
      1 ∉ S ∧ 1 ∉ T ∧
      Set.ncard S = 6 ∧ Set.ncard T = 6 ∧
      T = q '' S ∧
      (∀ x y : G, x⁻¹ * y ∈ S ↔ (q x)⁻¹ * q y ∈ T) ∧
      ¬ ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
