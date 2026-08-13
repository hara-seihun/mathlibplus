import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis.Claim3455

/-!
The dyadic interval is the half-open natural interval `N ≤ k < 2N`.
The coefficient sequence is complex-valued, so `Complex.normSq` is the
literal squared modulus appearing in the source formula.
-/

/-- The dyadic Baez--Duarte energy from claim 3455. -/
noncomputable def dyadicBaezDuarteEnergy (c : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico N (2 * N),
    Real.sqrt (k : ℝ) * Complex.normSq (c k)

@[simp] theorem dyadicBaezDuarteEnergy_zero (c : ℕ → ℂ) :
    dyadicBaezDuarteEnergy c 0 = 0 := by
  simp [dyadicBaezDuarteEnergy]

theorem dyadicBaezDuarteEnergy_nonneg (c : ℕ → ℂ) (N : ℕ) :
    0 ≤ dyadicBaezDuarteEnergy c N := by
  unfold dyadicBaezDuarteEnergy
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (Real.sqrt_nonneg _) (Complex.normSq_nonneg _)

end MathlibPlus.Analysis.Claim3455
