import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim17060

/-- Claim 17060: the displayed Lehmer polynomial is monic of degree ten over
    the integer polynomial ring. -/
theorem lehmerPolynomial_claim17060 :
    let L : Polynomial ℤ :=
      Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 -
        Polynomial.X ^ 3 + Polynomial.X + 1
    L.Monic ∧ L.natDegree = 10 := by
  dsimp
  have h1 :
      (Polynomial.X ^ 10 + Polynomial.X ^ 9 : Polynomial ℤ).natDegree = 10 := by
    calc
      _ = (Polynomial.X ^ 10 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp)
      _ = 10 := by simp
  have h2 :
      (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 : Polynomial ℤ).natDegree = 10 := by
    calc
      _ = (Polynomial.X ^ 10 + Polynomial.X ^ 9 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [h1]; simp)
      _ = 10 := h1
  have h3 :
      (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 : Polynomial ℤ).natDegree = 10 := by
    calc
      _ = (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [h2]; simp)
      _ = 10 := h2
  have h4 :
      (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 : Polynomial ℤ).natDegree = 10 := by
    calc
      _ = (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [h3]; simp)
      _ = 10 := h3
  have h5 :
      (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 : Polynomial ℤ).natDegree = 10 := by
    calc
      _ = (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [h4]; simp)
      _ = 10 := h4
  have h6 :
      (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 -
        Polynomial.X ^ 3 : Polynomial ℤ).natDegree = 10 := by
    calc
      _ = (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by rw [h5]; simp)
      _ = 10 := h5
  have h7 :
      (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 -
        Polynomial.X ^ 3 + Polynomial.X : Polynomial ℤ).natDegree = 10 := by
    calc
      _ = (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 -
        Polynomial.X ^ 3 : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by rw [h6]; simp)
      _ = 10 := h6
  have hdeg :
      (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 -
        Polynomial.X ^ 3 + Polynomial.X + 1 : Polynomial ℤ).natDegree = 10 := by
    calc
      _ = (Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
        Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 -
        Polynomial.X ^ 3 + Polynomial.X : Polynomial ℤ).natDegree :=
        Polynomial.natDegree_add_eq_left_of_natDegree_lt (by rw [h7]; norm_num)
      _ = 10 := h7
  constructor
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg]
    simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_one]
  · exact hdeg

end MathlibPlus.Algebra.Claim17060
