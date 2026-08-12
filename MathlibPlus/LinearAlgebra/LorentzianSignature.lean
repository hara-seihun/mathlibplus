import Mathlib

open scoped Matrix

namespace MathlibPlus.LinearAlgebra

/-!
Formalization of admitted claim 17594 (packet R-0061).  The source's
``one positive and one negative eigenvalue'' is represented by the two
explicit real spectral values of the displayed symmetric 2-by-2 matrix.
The characteristic-root equations are retained alongside membership in
` spectrum ℝ M`, rather than replacing the claim by the determinant sign
alone.
-/

/--
For nonzero wall currents, the displayed Maslov matrix is symmetric,
nondegenerate with the stated determinant, and has one positive and one
negative real spectral value.
-/
theorem lorentzianSignature_claim17594 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    let den : ℝ := a ^ 2 * b ^ 2 + 4
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      !![2 * a * b ^ 2 / den, -a * b * (a * b + 2) / den;
          -a * b * (a * b + 2) / den, 2 * a ^ 2 * b / den]
    let A : ℝ := M 0 0
    let B : ℝ := M 0 1
    let C : ℝ := M 1 1
    M.IsSymm ∧
      Matrix.det M = -a ^ 2 * b ^ 2 / den ∧
      Matrix.det M < 0 ∧
      ∃ (lamPlus lamMinus : ℝ),
        0 < lamPlus ∧ lamMinus < 0 ∧
        (lamPlus - A) * (lamPlus - C) - B ^ 2 = 0 ∧
        (lamMinus - A) * (lamMinus - C) - B ^ 2 = 0 ∧
        lamPlus ∈ spectrum ℝ M ∧
        lamMinus ∈ spectrum ℝ M := by
  dsimp
  let den : ℝ := a ^ 2 * b ^ 2 + 4
  let A : ℝ := 2 * a * b ^ 2 / den
  let B : ℝ := -a * b * (a * b + 2) / den
  let C : ℝ := 2 * a ^ 2 * b / den
  have hden : 0 < den := by
    dsimp [den]
    nlinarith [sq_nonneg (a * b)]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hdet : A * C - B ^ 2 = -a ^ 2 * b ^ 2 / den := by
    dsimp [A, B, C, den]
    field_simp
    ring
  have hdetneg : A * C - B ^ 2 < 0 := by
    rw [hdet]
    have : 0 < a ^ 2 * b ^ 2 :=
      mul_pos (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hb)
    exact div_neg_of_neg_of_pos (by nlinarith) hden
  have hdisc_eq : (A - C) ^ 2 + 4 * B ^ 2 =
      (A + C) ^ 2 - 4 * (A * C - B ^ 2) := by
    ring
  have hdisc : 0 < (A - C) ^ 2 + 4 * B ^ 2 := by
    rw [hdisc_eq]
    nlinarith [hdetneg]
  let s : ℝ := Real.sqrt ((A - C) ^ 2 + 4 * B ^ 2)
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (A - C) ^ 2 + 4 * B ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt (le_of_lt hdisc)]
  have htrace_disc : (A + C) ^ 2 < s ^ 2 := by
    nlinarith [hdetneg, hs2]
  have hs_gt_trace : A + C < s := by
    nlinarith
  have hs_gt_neg_trace : -(A + C) < s := by
    nlinarith
  let lamPlus : ℝ := ((A + C) + s) / 2
  let lamMinus : ℝ := ((A + C) - s) / 2
  have hlamPlus : 0 < lamPlus := by
    dsimp [lamPlus]
    nlinarith
  have hlamMinus : lamMinus < 0 := by
    dsimp [lamMinus]
    nlinarith
  have hroot (lam : ℝ)
      (hlam : (lam - ((A + C) / 2)) ^ 2 = s ^ 2 / 4) :
      (lam - A) * (lam - C) - B ^ 2 = 0 := by
    nlinarith [hs2]
  let M0 : Matrix (Fin 2) (Fin 2) ℝ := !![A, B; B, C]
  have hspec (lam : ℝ)
      (hroot_lam : (lam - A) * (lam - C) - B ^ 2 = 0) :
      lam ∈ spectrum ℝ M0 := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    rw [Matrix.charpoly_fin_two]
    rw [Polynomial.IsRoot.def]
    simp [M0, Matrix.trace_fin_two, Matrix.det_fin_two, pow_two]
    nlinarith [hroot_lam]
  have hpquad : (lamPlus - (A + C) / 2) ^ 2 = s ^ 2 / 4 := by
    dsimp [lamPlus]
    ring
  have hmquad : (lamMinus - (A + C) / 2) ^ 2 = s ^ 2 / 4 := by
    dsimp [lamMinus]
    ring
  refine ⟨?_, ?_, ?_, lamPlus, lamMinus, hlamPlus, hlamMinus, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · simpa [A, B, C, den, Matrix.det_fin_two, pow_two] using hdet
  · simpa [A, B, C, den, Matrix.det_fin_two, pow_two] using hdetneg
  · simpa [A, B, C, den] using hroot lamPlus hpquad
  · simpa [A, B, C, den] using hroot lamMinus hmquad
  · simpa [M0, A, B, C, den] using hspec lamPlus (hroot lamPlus hpquad)
  · simpa [M0, A, B, C, den] using hspec lamMinus (hroot lamMinus hmquad)

end MathlibPlus.LinearAlgebra
