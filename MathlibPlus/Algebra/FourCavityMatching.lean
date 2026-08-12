import MathlibPlus.Basic

namespace MathlibPlus.Algebra.FourCavityMatching

/-!
Formalization of admitted claim 24673.  `T` is the outer polynomial variable
and `w` is the coefficient polynomial variable.  The three displayed
coefficient-one equations explicitly subtract the common `w`-terms, leaving
`ab+cd`, `ac+bd`, and `ad+bc`.  The identities hold without the source's
pairwise-distinctness assumption, so no extra hypothesis is needed here.
-/

/-- The three four-cavity matching polynomials have the claimed coefficients. -/
theorem matching_coefficient_identities_claim24673 {R : Type*} [CommRing R]
    (a b c d : R) :
    let w : Polynomial R := Polynomial.X
    let T : Polynomial (Polynomial R) := Polynomial.X
    let f (x y : R) : Polynomial R :=
      (w + Polynomial.C x) * (w + Polynomial.C y)
    let H₀ := (T + Polynomial.C (f a b)) * (T + Polynomial.C (f c d))
    let H₁ := (T + Polynomial.C (f a c)) * (T + Polynomial.C (f b d))
    let H₂ := (T + Polynomial.C (f a d)) * (T + Polynomial.C (f b c))
    H₀.coeff 2 = 1 ∧
    H₁.coeff 2 = 1 ∧
    H₂.coeff 2 = 1 ∧
    H₀.coeff 0 = H₁.coeff 0 ∧
    H₁.coeff 0 = H₂.coeff 0 ∧
    H₀.coeff 1 =
      2 * (Polynomial.X : Polynomial R) ^ 2 +
        Polynomial.C (a + b + c + d) * Polynomial.X +
        Polynomial.C (a * b + c * d) ∧
    H₁.coeff 1 =
      2 * (Polynomial.X : Polynomial R) ^ 2 +
        Polynomial.C (a + b + c + d) * Polynomial.X +
        Polynomial.C (a * c + b * d) ∧
    H₂.coeff 1 =
      2 * (Polynomial.X : Polynomial R) ^ 2 +
        Polynomial.C (a + b + c + d) * Polynomial.X +
        Polynomial.C (a * d + b * c) := by
  dsimp
  have coeff_two (u v : Polynomial R) :
      (((Polynomial.X : Polynomial (Polynomial R)) + Polynomial.C u) *
          (Polynomial.X + Polynomial.C v)).coeff 2 = 1 := by
    have h :
        ((Polynomial.X : Polynomial (Polynomial R)) + Polynomial.C u) *
            (Polynomial.X + Polynomial.C v) =
          (Polynomial.X : Polynomial (Polynomial R)) ^ 2 +
            (Polynomial.C u + Polynomial.C v) * Polynomial.X +
            Polynomial.C u * Polynomial.C v := by
      ring
    rw [h]
    simp only [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  have coeff_one (u v : Polynomial R) :
      (((Polynomial.X : Polynomial (Polynomial R)) + Polynomial.C u) *
          (Polynomial.X + Polynomial.C v)).coeff 1 = u + v := by
    have h :
        ((Polynomial.X : Polynomial (Polynomial R)) + Polynomial.C u) *
            (Polynomial.X + Polynomial.C v) =
          (Polynomial.X : Polynomial (Polynomial R)) ^ 2 +
            (Polynomial.C u + Polynomial.C v) * Polynomial.X +
            Polynomial.C u * Polynomial.C v := by
      ring
    rw [h]
    simp only [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  have coeff_zero (u v : Polynomial R) :
      (((Polynomial.X : Polynomial (Polynomial R)) + Polynomial.C u) *
          (Polynomial.X + Polynomial.C v)).coeff 0 = u * v := by
    have h :
        ((Polynomial.X : Polynomial (Polynomial R)) + Polynomial.C u) *
            (Polynomial.X + Polynomial.C v) =
          (Polynomial.X : Polynomial (Polynomial R)) ^ 2 +
            (Polynomial.C u + Polynomial.C v) * Polynomial.X +
            Polynomial.C u * Polynomial.C v := by
      ring
    rw [h]
    simp only [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  have hsum₀ :
      (Polynomial.X + Polynomial.C a) * (Polynomial.X + Polynomial.C b) +
          (Polynomial.X + Polynomial.C c) * (Polynomial.X + Polynomial.C d) =
        2 * (Polynomial.X : Polynomial R) ^ 2 +
          Polynomial.C (a + b + c + d) * Polynomial.X +
          Polynomial.C (a * b + c * d) := by
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring
  have hsum₁ :
      (Polynomial.X + Polynomial.C a) * (Polynomial.X + Polynomial.C c) +
          (Polynomial.X + Polynomial.C b) * (Polynomial.X + Polynomial.C d) =
        2 * (Polynomial.X : Polynomial R) ^ 2 +
          Polynomial.C (a + b + c + d) * Polynomial.X +
          Polynomial.C (a * c + b * d) := by
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring
  have hsum₂ :
      (Polynomial.X + Polynomial.C a) * (Polynomial.X + Polynomial.C d) +
          (Polynomial.X + Polynomial.C b) * (Polynomial.X + Polynomial.C c) =
        2 * (Polynomial.X : Polynomial R) ^ 2 +
          Polynomial.C (a + b + c + d) * Polynomial.X +
          Polynomial.C (a * d + b * c) := by
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring
  constructor
  · exact coeff_two _ _
  constructor
  · exact coeff_two _ _
  constructor
  · exact coeff_two _ _
  constructor
  · rw [coeff_zero, coeff_zero]
    ring
  constructor
  · rw [coeff_zero, coeff_zero]
    ring
  constructor
  · rw [coeff_one]
    exact hsum₀
  constructor
  · rw [coeff_one]
    exact hsum₁
  · rw [coeff_one]
    exact hsum₂

end MathlibPlus.Algebra.FourCavityMatching
