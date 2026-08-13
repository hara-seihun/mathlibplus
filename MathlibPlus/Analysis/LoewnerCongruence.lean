import MathlibPlus.Analysis.EvenLoewner

open scoped BigOperators Matrix

namespace MathlibPlus.Analysis.EvenLoewner

/-- The algebraic distinct-node part of the change of variables `x = r^2`.
Under the two pointwise identities relating `H` to `L` and their derivatives,
the existing total-even matrix at positive distinct rates is the diagonal
congruence of the negative Loewner matrix at the squared rates. -/
theorem totalEvenLoewnerMatrix_congruent
    {n : ℕ} (L H : ℝ → ℝ) (r : Fin n → ℝ)
    (hpos : ∀ i, 0 < r i) (hinj : Function.Injective r)
    (hval : ∀ i, H (r i ^ 2) = L (r i) / r i)
    (hderiv : ∀ i, deriv H (r i ^ 2) =
      (r i * deriv L (r i) - L (r i)) / (2 * r i ^ 3)) :
    totalEvenLoewnerMatrix L r hpos hinj =
      let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j =>
        if r i ^ 2 = r j ^ 2 then -deriv H (r i ^ 2)
        else -(H (r i ^ 2) - H (r j ^ 2)) /
          (r i ^ 2 - r j ^ 2))
      Matrix.diagonal (fun i => 2 * r i) * B *
        Matrix.diagonal (fun i => 2 * r i) := by
  have hsq : ∀ {i j : Fin n}, i ≠ j → r i ^ 2 ≠ r j ^ 2 := by
    intro i j hij h
    have hne : r i ≠ r j := fun h' => hij (hinj h')
    apply hne
    nlinarith [hpos i, hpos j]
  dsimp [totalEvenLoewnerMatrix]
  have hdiag (M : Matrix (Fin n) (Fin n) ℝ) :
      Matrix.diagonal (fun i => 2 * r i) * M *
          Matrix.diagonal (fun i => 2 * r i) =
        fun i j => (2 * r i) * M i j * (2 * r j) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal]
  rw [hdiag]
  ext i j
  by_cases hij : i = j
  · subst j
    have hri : r i ≠ 0 := ne_of_gt (hpos i)
    simp [hderiv]
    field_simp [hri]
    ring
  · have hsq' := hsq hij
    have hri : r i ≠ 0 := ne_of_gt (hpos i)
    have hrj : r j ≠ 0 := ne_of_gt (hpos j)
    simp [hij, hsq', hval]
    field_simp [hri, hrj]
    ring

/-- A real diagonal congruence preserves positive semidefiniteness in both
 directions when every diagonal entry is nonzero. -/
theorem diagonalCongruence_posSemidef_iff
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d * M * Matrix.diagonal d).PosSemidef ↔ M.PosSemidef := by
  have hdiag_psd : ∀ (N : Matrix (Fin n) (Fin n) ℝ), N.PosSemidef →
      (Matrix.diagonal d * N * Matrix.diagonal d).PosSemidef := by
    intro N hN
    have hdt : (Matrix.diagonal d)ᴴ = Matrix.diagonal d := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.conjTranspose, Matrix.diagonal, Matrix.transpose]
      · have hji : j ≠ i := Ne.symm hij
        simp [Matrix.conjTranspose, Matrix.diagonal, Matrix.transpose, hij, hji]
    have h := hN.conjTranspose_mul_mul_same (Matrix.diagonal d)
    rw [hdt] at h
    exact h
  constructor
  · intro hM
    let di : Fin n → ℝ := fun i => (d i)⁻¹
    have hdt : (Matrix.diagonal di)ᴴ = Matrix.diagonal di := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.conjTranspose, Matrix.diagonal, Matrix.transpose]
      · have hji : j ≠ i := Ne.symm hij
        simp [Matrix.conjTranspose, Matrix.diagonal, Matrix.transpose, hij, hji]
    have h := hM.conjTranspose_mul_mul_same (Matrix.diagonal di)
    rw [hdt] at h
    have hinv : Matrix.diagonal di *
          (Matrix.diagonal d * M * Matrix.diagonal d) *
          Matrix.diagonal di = M := by
      ext i j
      simp [di, Matrix.mul_apply, Matrix.diagonal]
      field_simp [hd i, hd j]
    rw [hinv] at h
    exact h
  · intro hM
    exact hdiag_psd M hM

/-- A positive real diagonal congruence preserves the sign of a determinant. -/
theorem diagonalCongruence_det_neg_iff
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) :
    Matrix.det (Matrix.diagonal d * M * Matrix.diagonal d) < 0 ↔
      Matrix.det M < 0 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hp : 0 < (∏ i, d i) ^ 2 := by
    exact sq_pos_of_pos (Finset.prod_pos (fun i _ => hd i))
  constructor <;> intro h <;> nlinarith

end MathlibPlus.Analysis.EvenLoewner
