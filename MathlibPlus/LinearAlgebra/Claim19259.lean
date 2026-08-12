import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim19259

/-!
The displayed rank-one Schur bridge is formalized at the level of quadratic
forms.  `hAug` says that the block with upper-left block `G`, cross block
`v / 2`, and lower-right scalar `1` is positive on every `(x,t)`.  The
conclusion is positivity of the exact Schur-complement block
`G - vvᵀ / 4`; no symmetry or invertibility hypothesis beyond the stated Gram
positivity is added.
-/

/-- Positivity of the one-dimensional augmented Gram implies positivity of its
rank-one Schur defect, as in claim 19259. -/
theorem rankOneDefectSchurBridge_claim19259
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ι → ι → ℝ) (v : ι → ℝ)
    (hAug : ∀ (x : ι → ℝ) (t : ℝ),
      0 ≤
        (∑ i, ∑ j, x i * G i j * x j) +
          (∑ i, x i * (v i / 2)) * t +
          t * (∑ j, (v j / 2) * x j) + t * t) :
    ∀ x : ι → ℝ,
      0 ≤ ∑ i, ∑ j, x i * (G i j - v i * v j / 4) * x j := by
  intro x
  let s : ℝ := ∑ i, x i * v i
  have hleft : (∑ i, x i * (v i / 2)) = s / 2 := by
    calc
      (∑ i, x i * (v i / 2)) = ∑ i, (x i * v i) * (1 / 2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, x i * v i) * (1 / 2 : ℝ) := by
        rw [Finset.sum_mul]
      _ = s / 2 := by dsimp [s]; simp [div_eq_mul_inv]
  have hright : (∑ j, (v j / 2) * x j) = s / 2 := by
    calc
      (∑ j, (v j / 2) * x j) = ∑ j, (v j * x j) * (1 / 2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ j, v j * x j) * (1 / 2 : ℝ) := by
        rw [Finset.sum_mul]
      _ = s / 2 := by
        dsimp [s]
        have hs : (∑ j, v j * x j) = ∑ i, x i * v i := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [hs]
        simp [div_eq_mul_inv]
  have hdouble :
      (∑ i, ∑ j, (x i * v i) * (v j * x j)) =
        (∑ i, x i * v i) * (∑ j, v j * x j) := by
    calc
      (∑ i, ∑ j, (x i * v i) * (v j * x j)) =
          ∑ i, (x i * v i) * (∑ j, v j * x j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = (∑ i, x i * v i) * (∑ j, v j * x j) := by
        rw [Finset.sum_mul]
  have houter :
      (∑ i, ∑ j, x i * (v i * v j / 4) * x j) = s ^ 2 / 4 := by
    calc
      (∑ i, ∑ j, x i * (v i * v j / 4) * x j) =
          ∑ i, ∑ j, ((x i * v i) * (v j * x j)) / 4 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i, (∑ j, (x i * v i) * (v j * x j)) / 4 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_div]
      _ = (∑ i, ∑ j, (x i * v i) * (v j * x j)) / 4 := by
        rw [Finset.sum_div]
      _ = ((∑ i, x i * v i) * (∑ j, v j * x j)) / 4 := by rw [hdouble]
      _ = s ^ 2 / 4 := by
        dsimp [s]
        have hs : (∑ j, v j * x j) = ∑ i, x i * v i := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [hs]
        ring
  have h := hAug x (-(s / 2))
  rw [hleft, hright] at h
  have hq :
      (∑ i, ∑ j, x i * (G i j - v i * v j / 4) * x j) =
        (∑ i, ∑ j, x i * G i j * x j) - s ^ 2 / 4 := by
    calc
      (∑ i, ∑ j, x i * (G i j - v i * v j / 4) * x j) =
          ∑ i, ∑ j, (x i * G i j * x j - x i * (v i * v j / 4) * x j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ i, ∑ j, x i * G i j * x j) -
          (∑ i, ∑ j, x i * (v i * v j / 4) * x j) := by
        simp only [Finset.sum_sub_distrib]
      _ = (∑ i, ∑ j, x i * G i j * x j) - s ^ 2 / 4 := by rw [houter]
  rw [hq]
  nlinarith

end MathlibPlus.LinearAlgebra.Claim19259
