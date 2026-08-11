import Mathlib

/-!
# Axler-score tail-polynomial reduction

Statement-faithful formalization of admitted claim 1350 from packet `C-0089`.
The theorem isolates the exact algebraic comparison; it does not assert the
imported Dusart prime-counting estimate.
-/

namespace MathlibPlus.AxlerScoreTailPolynomial

/-- On the positive-denominator domain, the packet's four-term Dusart majorant
is strictly below the Axler-score target exactly when the displayed cubic is
positive. The common positive factor `x` has been cancelled from both bounds. -/
theorem dusartTailReduction (c L : ℝ) (hL : 0 < L)
    (hden : 0 < L - 1 - c / L) :
    1 / L * (1 + 1 / L + 2 / L ^ 2 + (759 : ℝ) / 100 / L ^ 3) <
        1 / (L - 1 - c / L) ↔
      0 < (c - 1) * L ^ 3 + (c + 2 - (759 : ℝ) / 100) * L ^ 2 +
        (2 * c + (759 : ℝ) / 100) * L + (759 : ℝ) / 100 * c := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hdenne : L - 1 - c / L ≠ 0 := ne_of_gt hden
  have hdenMul : (L - 1 - c / L) * L = L ^ 2 - L - c := by
    field_simp [hLne]
  have hquad : 0 < L ^ 2 - L - c := by
    rw [← hdenMul]
    exact mul_pos hden hL
  have hleft :
      1 / L * (1 + 1 / L + 2 / L ^ 2 + (759 : ℝ) / 100 / L ^ 3) =
        (L ^ 3 + L ^ 2 + 2 * L + (759 : ℝ) / 100) / L ^ 4 := by
    field_simp [hLne]
  have hright : 1 / (L - 1 - c / L) = L / (L ^ 2 - L - c) := by
    field_simp [hLne, hdenne]
  have hL4 : 0 < L ^ 4 := pow_pos hL 4
  rw [hleft, hright, div_lt_div_iff₀ hL4 hquad]
  ring_nf
  constructor <;> intro h <;> linarith

end MathlibPlus.AxlerScoreTailPolynomial
