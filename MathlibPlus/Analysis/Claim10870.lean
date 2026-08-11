import Mathlib

/-!
# Exact counterfeit impedance (claim 10870)

The witness polynomial is the real polynomial from the admitted counterfeit
calculation.  The Cayley expression is parameterized by `a`; its displayed
impedance variable is `x = a^2`.
-/

namespace MathlibPlus.Analysis.Claim10870

noncomputable def counterfeitPolynomial (z : ℝ) : ℝ :=
  ((z + (1 / 10 : ℝ)) ^ 2 + 1) * ((z + (2 / 5 : ℝ)) ^ 2 + 1)

noncomputable def psi (a : ℝ) : ℝ :=
  counterfeitPolynomial (-a) / counterfeitPolynomial a

noncomputable def unitHeightCayley (a : ℝ) : ℝ :=
  a * (1 - psi a) / (1 + psi a)

noncomputable def impedance (x : ℝ) : ℝ :=
  100 * x * (25 * x + 26) / (2500 * x ^ 2 + 5825 * x + 2929)

theorem counterfeitPolynomial_pos (a : ℝ) : 0 < counterfeitPolynomial a := by
  dsimp [counterfeitPolynomial]
  positivity

theorem unitHeightCayley_eq_impedance (a : ℝ) :
    unitHeightCayley a = impedance (a ^ 2) := by
  have ha : counterfeitPolynomial a ≠ 0 :=
    ne_of_gt (counterfeitPolynomial_pos a)
  have hma : counterfeitPolynomial (-a) ≠ 0 :=
    ne_of_gt (counterfeitPolynomial_pos (-a))
  have hsum : counterfeitPolynomial a + counterfeitPolynomial (-a) ≠ 0 := by
    exact ne_of_gt (add_pos (counterfeitPolynomial_pos a)
      (counterfeitPolynomial_pos (-a)))
  dsimp [unitHeightCayley, psi, impedance, counterfeitPolynomial]
  field_simp [ha, hma, hsum]
  ring

end MathlibPlus.Analysis.Claim10870
