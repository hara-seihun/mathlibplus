import Mathlib

namespace MathlibPlus.Algebra.RelativeWeylHeat

/-- Claim 7767: the two-state relative-Weyl heat family is stochastic, has
characteristic roots `1` and `lam`, obeys the multiplicative semigroup law,
and is invertible exactly away from `lam = 0`.  The explicit matrix below is
`((1 + lam) / 2) I + ((1 - lam) / 2) w` after expanding the swap matrix. -/
theorem relativeWeylHeat_claim7767
    (lam mu : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    let P : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t =>
      !![(1 + t) / 2, (1 - t) / 2;
         (1 - t) / 2, (1 + t) / 2]
    (∀ i : Fin 2, (∀ j : Fin 2, 0 ≤ P lam i j) ∧
      ∑ j : Fin 2, P lam i j = 1) ∧
    (P lam).charpoly =
      (Polynomial.X - Polynomial.C 1) *
        (Polynomial.X - Polynomial.C lam) ∧
    Matrix.det (P lam) = lam ∧
    P lam * P mu = P (lam * mu) ∧
    (IsUnit (P lam) ↔ lam ≠ 0) := by
  dsimp
  let P : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun t =>
    !![(1 + t) / 2, (1 - t) / 2;
       (1 - t) / 2, (1 + t) / 2]
  change (∀ i : Fin 2, (∀ j : Fin 2, 0 ≤ P lam i j) ∧
      ∑ j : Fin 2, P lam i j = 1) ∧
    (P lam).charpoly =
      (Polynomial.X - Polynomial.C 1) *
        (Polynomial.X - Polynomial.C lam) ∧
    Matrix.det (P lam) = lam ∧
    P lam * P mu = P (lam * mu) ∧
    (IsUnit (P lam) ↔ lam ≠ 0)
  have hstoch : ∀ i : Fin 2, (∀ j : Fin 2, 0 ≤ P lam i j) ∧
      ∑ j : Fin 2, P lam i j = 1 := by
    intro i
    constructor
    · intro j
      fin_cases i <;> fin_cases j <;> norm_num [P] <;>
        linarith [hlam, hlam1]
    · fin_cases i <;> simp [P, Fin.sum_univ_two] <;> ring
  have hchar : (P lam).charpoly =
      (Polynomial.X - Polynomial.C 1) *
        (Polynomial.X - Polynomial.C lam) := by
    rw [Matrix.charpoly_fin_two]
    simp [P, Matrix.trace_fin_two, Matrix.det_fin_two, Polynomial.C_mul,
      Polynomial.C_add, Polynomial.C_sub]
    have hc' :
        (1 + lam) / 2 * ((1 + lam) / 2) -
            (1 - lam) / 2 * ((1 - lam) / 2) = lam := by
      ring
    rw [← Polynomial.C_mul, ← Polynomial.C_mul, ← Polynomial.C_sub, hc']
    ring
  have hdet : Matrix.det (P lam) = lam := by
    simp [P, Matrix.det_fin_two]
    ring
  have hmul : P lam * P mu = P (lam * mu) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hunit : IsUnit (P lam) ↔ lam ≠ 0 := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero]
  exact ⟨hstoch, hchar, hdet, hmul, hunit⟩

end MathlibPlus.Algebra.RelativeWeylHeat
