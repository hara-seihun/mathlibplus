import Mathlib

namespace MathlibPlus.LinearAlgebra

open scoped BigOperators

/-- A finite real symmetric `Z`-matrix whose row sums are nonnegative is
positive semidefinite.  This is the derivative `M`-matrix lemma in admitted
claim 217. -/
theorem symmetricZMatrix_psd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ)
    (hsymm : ∀ i j, M i j = M j i)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hrow : ∀ i, 0 ≤ ∑ j, M i j) :
    M.PosSemidef := by
  have hherm : M.IsHermitian := by
    ext i j
    simpa [hsymm]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro x
  rw [show star x = x by rfl]
  have hswap :
      (∑ i, ∑ j, M i j * x j ^ 2) = ∑ i, ∑ j, M i j * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm]
  have hswapHalf :
      (∑ i, ∑ j, M i j * x j ^ 2 * (-1 / 2 : ℝ)) =
        ∑ i, ∑ j, M i j * x i ^ 2 * (-1 / 2 : ℝ) := by
    simpa only [Finset.sum_mul] using
      congrArg (fun z : ℝ => z * (-1 / 2 : ℝ)) hswap
  have hfactor :
      (∑ i, ∑ j, M i j * x i ^ 2 * (-1 / 2 : ℝ)) =
        (∑ i, ∑ j, M i j * x i ^ 2) * (-1 / 2 : ℝ) := by
    simp only [Finset.sum_mul]
  have hfactor' :
      (∑ i, ∑ j, M i j * (x i ^ 2 * (-1 / 2 : ℝ))) =
        (∑ i, ∑ j, M i j * x i ^ 2) * (-1 / 2 : ℝ) := by
    simpa only [mul_assoc] using hfactor
  have hid :
      x ⬝ᵥ M.mulVec x =
        (∑ i, (∑ j, M i j) * x i ^ 2) +
          (1 / 2 : ℝ) * ∑ i, ∑ j, (-M i j) * (x i - x j) ^ 2 := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [show (1 / 2 : ℝ) = 1 / 2 by rfl]
    ring_nf
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_mul, Finset.mul_sum]
    rw [hswapHalf]
    simp only [mul_comm, mul_left_comm, mul_assoc]
    rw [hfactor']
    ring
  rw [hid]
  apply add_nonneg
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hrow i) (sq_nonneg _)
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i = j
    · subst j
      simp
    · exact mul_nonneg (neg_nonneg.mpr (hoff i j hij)) (sq_nonneg _)

/-- Consequently, a differentiable matrix path whose derivative satisfies the
symmetric `Z`-matrix and row-sum hypotheses is Loewner monotone, expressed
without introducing a new order as monotonicity of every quadratic form. -/
theorem loewnerMonotone_of_derivative_symmetricZ
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F F' : ℝ → Matrix ι ι ℝ)
    (hderiv : ∀ t i j, HasDerivAt (fun s => F s i j) (F' t i j) t)
    (hsymm : ∀ t i j, F' t i j = F' t j i)
    (hoff : ∀ t i j, i ≠ j → F' t i j ≤ 0)
    (hrow : ∀ t i, 0 ≤ ∑ j, F' t i j) :
    ∀ v : ι → ℝ, Monotone (fun t => v ⬝ᵥ (F t).mulVec v) := by
  intro v
  have hq (t : ℝ) : HasDerivAt (fun s => v ⬝ᵥ (F s).mulVec v)
      (v ⬝ᵥ (F' t).mulVec v) t := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    have hi (i : ι) : HasDerivAt
        (fun s => ∑ j, v i * (F s i j * v j))
        (∑ j, v i * (F' t i j * v j)) t := by
      have hraw := HasDerivAt.sum (u := Finset.univ) fun j _ =>
        ((hderiv t i j).const_mul (v i)).mul_const (v j)
      have hraw' : HasDerivAt
          (∑ j, fun s => v i * (F s i j * v j))
          (∑ j, v i * (F' t i j * v j)) t := by
        simpa only [mul_assoc] using hraw
      apply hraw'.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun s => by simp
    have hraw := HasDerivAt.sum (u := Finset.univ) fun i _ => hi i
    have hraw' : HasDerivAt
        (∑ i, fun s => ∑ j, v i * (F s i j * v j))
        (∑ i, ∑ j, v i * (F' t i j * v j)) t := by
      exact hraw
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s => by simp
  apply monotone_of_deriv_nonneg
  · exact fun t => (hq t).differentiableAt
  · intro t
    rw [(hq t).deriv]
    have hpsd : (F' t).PosSemidef :=
      symmetricZMatrix_psd (F' t) (hsymm t) (hoff t) (hrow t)
    simpa using hpsd.dotProduct_mulVec_nonneg v

end MathlibPlus.LinearAlgebra
