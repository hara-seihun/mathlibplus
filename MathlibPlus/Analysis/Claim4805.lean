import Mathlib

namespace MathlibPlus.Analysis.Claim4805

open Polynomial
noncomputable section

/-- The central-Charlier polynomial recurrence from the admitted definition
packet `D-0055`, with `a = 5/4`. -/
def centralCharlierPolynomial_claim4805 : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 =>
      X * derivative (centralCharlierPolynomial_claim4805 n) +
        (C (5 / 4) - X) * centralCharlierPolynomial_claim4805 n

lemma q_degree_claim4805 :
    (C (5 / 4) - X : Polynomial ℚ).natDegree = 1 := by
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
  · norm_num
  · norm_num

lemma q_ne_claim4805 :
    (C (5 / 4) - X : Polynomial ℚ) ≠ 0 := by
  intro h
  have hd := congrArg Polynomial.natDegree h
  rw [q_degree_claim4805] at hd
  simp at hd

theorem centralCharlierPolynomial_properties_claim4805 : ∀ n : ℕ,
    centralCharlierPolynomial_claim4805 n ≠ 0 ∧
      (centralCharlierPolynomial_claim4805 n).natDegree = n ∧
      (centralCharlierPolynomial_claim4805 n).coeff n = (-1 : ℚ)^n := by
  intro n
  induction n with
  | zero =>
      simp [centralCharlierPolynomial_claim4805]
  | succ n ih =>
      cases n with
      | zero =>
          norm_num [centralCharlierPolynomial_claim4805, q_ne_claim4805,
            q_degree_claim4805]
      | succ n =>
          rcases ih with ⟨ihne, ihdeg, ihcoeff⟩
          have hderiv_ne :
              derivative (centralCharlierPolynomial_claim4805 (n + 1)) ≠ 0 := by
            rw [Polynomial.derivative_ne_zero]
            omega
          have hDdeg :
              (derivative (centralCharlierPolynomial_claim4805 (n + 1))).natDegree = n := by
            rw [Polynomial.natDegree_derivative, ihdeg]
            omega
          have hAdeg :
              (X * derivative (centralCharlierPolynomial_claim4805 (n + 1))).natDegree =
                n + 1 := by
            rw [Polynomial.natDegree_X_mul hderiv_ne, hDdeg]
          have hQdeg :
              (C (5 / 4) - X : Polynomial ℚ).natDegree = 1 := q_degree_claim4805
          have hQne :
              (C (5 / 4) - X : Polynomial ℚ) ≠ 0 := q_ne_claim4805
          have hBdeg :
              ((C (5 / 4) - X) * centralCharlierPolynomial_claim4805 (n + 1)).natDegree =
                n + 2 := by
            rw [Polynomial.natDegree_mul hQne ihne, hQdeg, ihdeg]
            omega
          have hnat :
              (centralCharlierPolynomial_claim4805 (n + 2)).natDegree = n + 2 := by
            rw [centralCharlierPolynomial_claim4805,
              Polynomial.natDegree_add_eq_right_of_natDegree_lt]
            · exact hBdeg
            · rw [hAdeg, hBdeg]
              omega
          have hne : centralCharlierPolynomial_claim4805 (n + 2) ≠ 0 := by
            intro h
            have hd := congrArg Polynomial.natDegree h
            rw [hnat] at hd
            simp at hd
          have hcoeff :
              (centralCharlierPolynomial_claim4805 (n + 2)).coeff (n + 2) =
                (-1 : ℚ)^(n + 2) := by
            rw [centralCharlierPolynomial_claim4805, Polynomial.coeff_add]
            have hAzero :
                (X * derivative (centralCharlierPolynomial_claim4805 (n + 1))).coeff
                    (n + 2) = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hAdeg]; omega)
            rw [hAzero, sub_mul, Polynomial.coeff_sub,
              Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
            have hPzero :
                (centralCharlierPolynomial_claim4805 (n + 1)).coeff (n + 2) = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ihdeg]; omega)
            rw [hPzero, ihcoeff]
            ring
          exact ⟨hne, hnat, hcoeff⟩

/-- The exact degree assertion from claim 4805. -/
theorem centralCharlierPolynomial_degree_claim4805 (n : ℕ) :
    (centralCharlierPolynomial_claim4805 n).natDegree = n :=
  (centralCharlierPolynomial_properties_claim4805 n).2.1

/-- The exact leading-coefficient assertion from claim 4805. -/
theorem centralCharlierPolynomial_leadingCoeff_claim4805 (n : ℕ) :
    (centralCharlierPolynomial_claim4805 n).coeff n = (-1 : ℚ)^n :=
  (centralCharlierPolynomial_properties_claim4805 n).2.2

end
end MathlibPlus.Analysis.Claim4805
