import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

namespace MathlibPlus.LinearAlgebra.Claim11220

open scoped BigOperators

/--
Claim 11220.  The rows indexed by `Fin M` are the first `M` positive even
powers, and the columns are the distinct positive labels.  The determinant is
the displayed product, so the coefficient matrix is nonsingular.
-/
theorem shellMomentVandermonde_determinant
    (M : ℕ) (n : Fin M → ℝ)
    (hpos : ∀ j, 0 < n j) (hinj : Function.Injective n) :
    Matrix.det (fun i j : Fin M => (n j) ^ (2 * (i.val + 1))) =
      (∏ j : Fin M, n j ^ 2) *
        ∏ i : Fin M, ∏ j ∈ Finset.Ioi i, (n j ^ 2 - n i ^ 2) := by
  let v : Fin M → ℝ := fun j => n j ^ 2
  let D : Matrix (Fin M) (Fin M) ℝ := Matrix.diagonal v
  let V : Matrix (Fin M) (Fin M) ℝ := (Matrix.vandermonde v).transpose
  have hv : Function.Injective v := by
    intro i j hij
    dsimp [v] at hij
    have hi := hpos i
    have hj := hpos j
    have hfactor : (n i - n j) * (n i + n j) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hdiff | hsum
    · exact hinj (sub_eq_zero.mp hdiff)
    · linarith
  have hmat : (fun i j : Fin M => (n j) ^ (2 * (i.val + 1))) =
      V * D := by
    funext i j
    rw [Matrix.mul_apply]
    classical
    rw [Finset.sum_eq_single j]
    · simp [V, D, v, Matrix.vandermonde_apply, Matrix.diagonal,
        pow_add, Nat.mul_add]
      rw [pow_mul]
      exact Or.inl rfl
    · intro b hb hbj
      simp [D, Matrix.diagonal, hbj]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  rw [hmat, Matrix.det_mul, Matrix.det_transpose, Matrix.det_vandermonde,
    Matrix.det_diagonal]
  simp [v, mul_comm, mul_left_comm, mul_assoc]

end MathlibPlus.LinearAlgebra.Claim11220
