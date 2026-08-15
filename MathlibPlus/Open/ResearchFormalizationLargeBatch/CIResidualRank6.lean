import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim59966_rankSixResidualCellBounds : Prop := by
  classical
  exact ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    let R := ZMod p
    let V := Fin 6 → R
    ∀ (S T : Set V),
      0 ∉ S → 0 ∉ T →
      (∀ x ∈ S, -x ∈ S) → (∀ x ∈ T, -x ∈ T) →
      (∃ f : V → V,
        Function.Bijective f ∧
          ∀ x y, (y - x ∈ S ↔ f y - f x ∈ T)) →
      (∀ e : V ≃ₗ[R] V, e '' S ≠ T) →
      let Sstar : Set V := Set.univ \ (S ∪ {0})
      Submodule.span R S = ⊤ ∧
        Submodule.span R Sstar = ⊤ ∧
        p + 1 ≤ S.ncard ∧ S.ncard ≤ p ^ 6 - p - 2

end MathlibPlus.Open.ResearchFormalizationLargeBatch
