import Mathlib

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators ENNReal MeasureTheory Topology

namespace MathlibPlus.Open.Analysis.O0336.Claim15512

/-- A signed Borel measure is finitely atomic on a right half-open neighborhood of `a`.
The equality uses the signed-measure restriction and the actual Dirac measures. -/
def FinitelyAtomicRightOf (μ : SignedMeasure ℝ) (a : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∃ m : ℕ, ∃ α : Fin m → ℝ, ∃ c : Fin m → ℝ,
      (∀ j, c j ≠ 0) ∧
      (∀ j, a ≤ α j ∧ α j < a + δ) ∧
      μ.restrict (Set.Ico a (a + δ)) =
        ∑ j : Fin m, (c j) • (Measure.dirac (α j)).toSignedMeasure

/-- The lower endpoint of the closed support cannot have zero mass under a finite
local atomic representation. -/
def lowerSupportEndpointNonzeroAtom : Prop :=
  ∀ (μ : SignedMeasure ℝ) (a : ℝ),
    IsLeast μ.totalVariation.support a →
      FinitelyAtomicRightOf μ a →
        μ {a} ≠ 0

end MathlibPlus.Open.Analysis.O0336.Claim15512
