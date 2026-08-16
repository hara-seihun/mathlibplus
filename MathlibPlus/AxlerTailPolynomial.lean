import Mathlib

/-!
# Axler tail-polynomial comparison

Statement-faithful formalization of admitted claim 985, extracted from Record 11
of source record `C-0064`. This does not assert the imported Dusart
prime-counting bound or the packet's finite computational audit.
-/

namespace MathlibPlus.AxlerTailPolynomial

/-- Comparing the packet's four-term prime-counting majorant with denominator
coefficient `1.070` is exactly equivalent to positivity of its displayed cubic.
The hypothesis is precisely the positive-denominator range in the claim. -/
theorem dusartTo1070Comparison (L : ℝ) (hL : (107 : ℝ) / 100 < L) :
    1 / L *
          (1 + 1 / L + 2 / L ^ 2 + (759 : ℝ) / 100 / L ^ 3) <
        1 / (L - (107 : ℝ) / 100) ↔
      0 < (7 : ℝ) / 100 * L ^ 3 - (93 : ℝ) / 100 * L ^ 2 -
        (545 : ℝ) / 100 * L + (81213 : ℝ) / 10000 := by
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hsubpos : 0 < L - (107 : ℝ) / 100 := by linarith
  have hleft :
      1 / L * (1 + 1 / L + 2 / L ^ 2 + (759 : ℝ) / 100 / L ^ 3) =
        (L ^ 3 + L ^ 2 + 2 * L + (759 : ℝ) / 100) / L ^ 4 := by
    field_simp [hLne]
  have hL4pos : 0 < L ^ 4 := pow_pos hLpos 4
  rw [hleft, div_lt_div_iff₀ hL4pos hsubpos]
  ring_nf
  constructor <;> intro h <;> linarith

end MathlibPlus.AxlerTailPolynomial
