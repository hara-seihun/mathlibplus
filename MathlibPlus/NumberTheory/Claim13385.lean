import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc

open scoped ArithmeticFunction.Moebius

namespace MathlibPlus.NumberTheory.Claim13385

/-- Complementation inside a squarefree primorial.  The parameter `r` is the
number of distinct prime factors of `Q`; the statement is written for an
arbitrary squarefree `Q`, which includes the primorial `Q_y` in the source. -/
theorem mobius_divisor_complement {Q d e r : ℕ}
    (hQ : Squarefree Q) (hd : d ∣ Q) (he : e = Q / d)
    (hr : r = ArithmeticFunction.cardFactors Q) :
    (-1 : ℤ) ^ r * (ArithmeticFunction.moebius d : ℤ) =
      ArithmeticFunction.moebius e := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    simp at hd
    exact hQ0 hd
  have hde : d * e = Q := by
    rw [he]
    exact Nat.mul_div_cancel' hd
  have he_dvd : e ∣ Q := by
    rw [← hde]
    exact dvd_mul_left _ _
  have hd_sq : Squarefree d := hQ.squarefree_of_dvd hd
  have he_sq : Squarefree e := hQ.squarefree_of_dvd he_dvd
  have he0 : e ≠ 0 := he_sq.ne_zero
  rw [ArithmeticFunction.moebius_apply_of_squarefree hd_sq,
    ArithmeticFunction.moebius_apply_of_squarefree he_sq, hr]
  have hcards := ArithmeticFunction.cardFactors_mul hd0 he0
  rw [hde] at hcards
  rw [hcards, pow_add]
  calc
    (-1 : ℤ) ^ ArithmeticFunction.cardFactors d *
          (-1 : ℤ) ^ ArithmeticFunction.cardFactors e *
          (-1 : ℤ) ^ ArithmeticFunction.cardFactors d =
        (-1 : ℤ) ^ ArithmeticFunction.cardFactors e *
          ((-1 : ℤ) ^ ArithmeticFunction.cardFactors d *
            (-1 : ℤ) ^ ArithmeticFunction.cardFactors d) := by ring
    _ = (-1 : ℤ) ^ ArithmeticFunction.cardFactors e * 1 := by
      rw [← pow_add]
      simp
    _ = (-1 : ℤ) ^ ArithmeticFunction.cardFactors e := by ring

end MathlibPlus.NumberTheory.Claim13385
