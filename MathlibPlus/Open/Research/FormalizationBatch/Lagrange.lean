import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

open scoped BigOperators

/-- Pairwise distinct rational profile nodes, with the four nodes indexed by `Fin 4`. -/
def DistinctProfileNodes (s : Fin 4 → ℚ) : Prop :=
  Function.Injective s

/-- The cubic Lagrange coefficient at one of four profile nodes. -/
noncomputable def cubicLagrangeCoefficient (s : Fin 4 → ℚ) (i : Fin 4) : ℚ :=
  (Finset.prod (Finset.univ.erase i) (fun j => s i - s j))⁻¹

/-- A concrete primitive/no-common-divisor condition for four integer weights. -/
def PrimitiveIntegerWeights (n : Fin 4 → ℤ) : Prop :=
  ∀ d : ℕ, 0 < d → (∀ i, (d : ℤ) ∣ n i) → d = 1

/-- The sign counts used in the ordered-node conclusion. -/
def ExactlyTwoPositive (n : Fin 4 → ℤ) : Prop :=
  (Finset.univ.filter (fun i => 0 < n i)).card = 2

/-- The sign counts used in the ordered-node conclusion. -/
def ExactlyTwoNegative (n : Fin 4 → ℤ) : Prop :=
  (Finset.univ.filter (fun i => n i < 0)).card = 2

/-- Translation leaves each of the four cubic Lagrange coefficients unchanged. -/
def translatedCubicCoefficientInvariant : Prop :=
  ∀ (s : Fin 4 → ℚ) (a : ℚ),
    DistinctProfileNodes s →
    ∀ i, cubicLagrangeCoefficient (fun j => s j + a) i = cubicLagrangeCoefficient s i

/-- A common translation can avoid zero at all four distinct nodes. -/
def translationToNonzero : Prop :=
  ∀ (s : Fin 4 → ℚ),
    DistinctProfileNodes s →
    ∃ a : ℚ, ∀ i, s i + a ≠ 0

/-- A positive denominator-clearing scale can be chosen primitive and has the
three cubic Lagrange moment identities. -/
def primitiveIntegralLagrangeScale : Prop :=
  ∀ (s : Fin 4 → ℚ),
    DistinctProfileNodes s →
    ∃ (N : ℕ) (n : Fin 4 → ℤ),
      0 < N ∧
      PrimitiveIntegerWeights n ∧
      (∀ i, (n i : ℚ) = (N : ℚ) * cubicLagrangeCoefficient s i) ∧
      (∑ i : Fin 4, (n i : ℚ)) = 0 ∧
      (∑ i : Fin 4, (n i : ℚ) * s i) = 0 ∧
      (∑ i : Fin 4, (n i : ℚ) * s i ^ 2) = 0

/-- For strictly ordered nodes, every positive integral Lagrange scale has
alternating signs; primitiveness is only a normalization of that scale. -/
def sortedLagrangeSigns : Prop :=
  ∀ (s : Fin 4 → ℚ) (N : ℕ) (n : Fin 4 → ℤ),
    DistinctProfileNodes s →
    s 0 < s 1 ∧ s 1 < s 2 ∧ s 2 < s 3 →
    0 < N →
    PrimitiveIntegerWeights n →
    (∀ i, (n i : ℚ) = (N : ℚ) * cubicLagrangeCoefficient s i) →
    ExactlyTwoPositive n ∧
    ExactlyTwoNegative n ∧
    n 0 < 0 ∧ 0 < n 1 ∧ n 2 < 0 ∧ 0 < n 3

/-- Claim 43302: translation invariance, nonzero translation, primitive
integral scaling with the three vanishing moments, and the ordered sign
pattern are recorded together without identifying normalization with the
moment equations. -/
def claim43302 : Prop :=
  translatedCubicCoefficientInvariant ∧
  translationToNonzero ∧
  primitiveIntegralLagrangeScale ∧
  sortedLagrangeSigns

end MathlibPlus.Open.Research.FormalizationBatch
