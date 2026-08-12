import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.Analysis

/-!
Formalization of admitted claim 21915.

The source uses a slice budget and writes the product over `j < n` while the
reported lower-bound factor is `n - 1`.  This theorem makes the intended
`n - 1` slice variables explicit as `Fin (n - 1)`, and exposes the budget and
fixed-product equations as hypotheses.  The source does not specify domains
for the weights, the norm coefficient, or the slice variables; positivity and
a nonzero denominator are therefore explicit fidelity-review premises.
-/

/-- Weighted AM--GM lower bound for the explicit `n - 1`-variable slice budget
from claim 21915. -/
theorem sliceNormLowerBound_claim21915
    {n : ℕ} (hn : 2 ≤ n) (m H N : ℝ) (w x : Fin (n - 1) → ℝ) (cT : ℝ)
    (_hw : ∀ j, 0 < w j) (hx : ∀ j, 0 < x j) (_hN : 0 < N) (_hc : cT ≠ 0)
    (hbudget : H = m + 2 * ∑ j, x j)
    (hprod : (∏ j, x j) = N * (∏ j, w j) / |cT|) :
    H ≥ m + 2 * ((n - 1 : ℕ) : ℝ) *
      (N * (∏ j, w j) / |cT|) ^ ((n - 1 : ℕ) : ℝ)⁻¹ := by
  let k : ℕ := n - 1
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hgm := Real.geom_mean_le_arith_mean
    (s := (Finset.univ : Finset (Fin k)))
    (w := fun _ : Fin k => (1 : ℝ))
    (z := fun j : Fin k => x j)
    (by simp)
    (by simpa using (show (0 : ℝ) < k by exact_mod_cast hk))
    (by intro j hj; exact (hx j).le)
  have hgm' :
      (∏ j : Fin k, x j) ^ (k : ℝ)⁻¹ ≤
        (∑ j : Fin k, x j) / (k : ℝ) := by
    simpa [Finset.prod_eq_multiset_prod, Real.rpow_one, hk.ne'] using hgm
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hsum : (k : ℝ) * (∏ j : Fin k, x j) ^ (k : ℝ)⁻¹ ≤ ∑ j : Fin k, x j := by
    calc
      (k : ℝ) * (∏ j : Fin k, x j) ^ (k : ℝ)⁻¹ ≤
          (k : ℝ) * ((∑ j : Fin k, x j) / (k : ℝ)) :=
        (mul_le_mul_of_nonneg_left hgm' hkR.le)
      _ = ∑ j : Fin k, x j := by field_simp
  dsimp [k] at hsum ⊢
  have hsum' := hsum
  rw [hprod] at hsum'
  rw [hbudget]
  nlinarith [hsum']

end MathlibPlus.Analysis
