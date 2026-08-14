import Mathlib

namespace MathlibPlus.Analysis.Claim968

private lemma derivativeValue_eq_factorial_coeff (f : Polynomial ℝ) (n : ℕ) :
    ((Polynomial.derivative^[n]) f).eval 0 =
      (Nat.factorial n : ℝ) * f.coeff n := by
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative, Nat.zero_add,
    Nat.descFactorial_self]
  norm_num [nsmul_eq_mul]

private lemma derivativeValue_eq_zero_of_natDegree_le_five
    {f : Polynomial ℝ} (hdeg : f.natDegree ≤ 5) {n : ℕ} (hn : 6 ≤ n) :
    ((Polynomial.derivative^[n]) f).eval 0 = 0 := by
  rw [derivativeValue_eq_factorial_coeff]
  have hlt : f.natDegree < n := lt_of_le_of_lt hdeg (by omega)
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

/-- A degree-at-most-five polynomial has a zero last column in the order-seven
reversed derivative Hankel matrix, and consequently its order-seven determinant
vanishes. -/
theorem support_at_most_five_vanishing_claim968
    {f : Polynomial ℝ} (hdeg : f.natDegree ≤ 5) :
    let H : Matrix (Fin 7) (Fin 7) ℝ := fun i j =>
      ((Polynomial.derivative^[6 + j.1 - i.1]) f).eval 0
    (∀ i : Fin 7, H i 6 = 0) ∧ H.det = 0 := by
  dsimp
  constructor
  · intro i
    have h : 6 ≤ 6 + 6 - i.1 := by omega
    exact derivativeValue_eq_zero_of_natDegree_le_five hdeg h
  · apply Matrix.det_eq_zero_of_column_eq_zero 6
    intro i
    have h : 6 ≤ 6 + 6 - i.1 := by omega
    exact derivativeValue_eq_zero_of_natDegree_le_five hdeg h

end MathlibPlus.Analysis.Claim968
