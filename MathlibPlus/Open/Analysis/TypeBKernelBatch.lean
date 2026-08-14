import Mathlib

namespace MathlibPlus.Open.Analysis.TypeBKernelBatch

noncomputable def typeBFoldedKernel (c y z : ℝ) : ℝ :=
  Real.exp (-(z - y) / c) * (if z ≥ y then 1 else 0) +
    Real.exp (-(z + y) / c)

def positiveTN2 (K : ℝ → ℝ → ℝ) : Prop :=
  ∀ y₁ y₂ z₁ z₂ : ℝ,
    0 < y₁ → y₁ < y₂ → 0 < z₁ → z₁ < z₂ →
    0 ≤ K y₁ z₁ * K y₂ z₂ - K y₁ z₂ * K y₂ z₁

/-- Claim 19458: the folded Type-B one-step kernel has the displayed two
summands. -/
def foldedTypeBOneStepKernel_claim19458 : Prop :=
  ∀ (c y z : ℝ), 0 < c → 0 < y → 0 < z →
    typeBFoldedKernel c y z =
      Real.exp (-(z - y) / c) * (if z ≥ y then 1 else 0) +
        Real.exp (-(z + y) / c)

/-- Claim 19460: the folded kernel fails total nonnegativity already at order
 two for every positive scale. -/
def foldedTypeBKernelNotTotallyNonnegative_claim19460 : Prop :=
  ∀ c : ℝ, 0 < c →
    ¬ positiveTN2 (typeBFoldedKernel c) ∧
    ∃ y₁ y₂ z₁ z₂ : ℝ,
      0 < y₁ ∧ y₁ < y₂ ∧ 0 < z₁ ∧ z₁ < z₂ ∧
      typeBFoldedKernel c y₁ z₁ * typeBFoldedKernel c y₂ z₂ -
        typeBFoldedKernel c y₁ z₂ * typeBFoldedKernel c y₂ z₁ < 0

end MathlibPlus.Open.Analysis.TypeBKernelBatch
