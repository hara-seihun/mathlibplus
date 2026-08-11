import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory

noncomputable section

/-- The positive-index Möbius inverse profile from claim 2473. -/
def claim2473PhiPlus (u : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then ((ArithmeticFunction.moebius n : ℤ) : ℝ) * g (n * u)
    else 0

lemma claim2473_term_zero_of_support {B u : ℝ} {n : ℕ} {g : ℝ → ℝ}
    (hu : 0 < u) (hnu : B / u ≤ (n : ℝ))
    (hg : ∀ x : ℝ, x < 1 ∨ B ≤ x → g x = 0) :
    (if 0 < n then ((ArithmeticFunction.moebius n : ℤ) : ℝ) * g (n * u)
      else 0) = 0 := by
  have hBnu : B ≤ (n : ℝ) * u := (div_le_iff₀ hu).mp hnu
  by_cases hn : 0 < n
  · simp [hn, hg ((n : ℝ) * u) (Or.inr hBnu)]
  · simp [hn]

/-- If `g` is supported in `[1,B)`, only the finite set of indices below the
cutoff `B/u` contributes to the positive-index Möbius profile. -/
theorem claim2473PhiPlus_eq_finite_sum
    {B u : ℝ} (hu : 1 ≤ u) (g : ℝ → ℝ)
    (hg : ∀ x : ℝ, x < 1 ∨ B ≤ x → g x = 0) :
    claim2473PhiPlus u g =
      ∑ n ∈ Finset.range (Nat.ceil (B / u)),
        if 0 < n then ((ArithmeticFunction.moebius n : ℤ) : ℝ) * g (n * u)
        else 0 := by
  rw [claim2473PhiPlus]
  apply tsum_eq_sum
  intro n hn
  have hceil : (Nat.ceil (B / u) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.le_of_not_gt (by simpa using hn))
  have hBu : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hcut : B / u ≤ (n : ℝ) :=
    (Nat.le_ceil (B / u)).trans hceil
  exact claim2473_term_zero_of_support hBu hcut hg

end

end MathlibPlus.NumberTheory
