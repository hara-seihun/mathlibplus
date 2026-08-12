import MathlibPlus.Basic
import Mathlib.Algebra.Group.ForwardDiff

namespace MathlibPlus.Analysis

open scoped fwdDiff

/-- The explicit completely monotone finite-difference core of claim 9505. -/
theorem completelyMonotoneJacobi_claim9505 (k n : ℕ) :
    0 < (-1 : ℝ) ^ k *
      ((Δ_[1])^[k] ((Δ_[1])^[2]
        (fun n : ℕ => (99 / 400 : ℝ) * n -
          (1 / 20 : ℝ) * (1 - (20 : ℝ)⁻¹ ^ n)))) n := by
  let r : ℝ := (20 : ℝ)⁻¹
  have hgeom (m : ℕ) :
      (Δ_[1])^[m] (fun n : ℕ => r ^ n) =
        fun n : ℕ => (r - 1) ^ m * r ^ n := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      ext j
      simp only [fwdDiff]
      rw [pow_succ]
      ring
  have hsecond :
      (Δ_[1])^[2]
        (fun n : ℕ => (99 / 400 : ℝ) * n -
          (1 / 20 : ℝ) * (1 - r ^ n)) =
        fun n : ℕ => (1 / 20 : ℝ) * (r - 1) ^ 2 * r ^ n := by
    funext j
    simp [Function.iterate_succ_apply', fwdDiff, pow_succ]
    ring
  have hconst :
      (fun n : ℕ => (1 / 20 : ℝ) * (r - 1) ^ 2 * r ^ n) =
        ((1 / 20 : ℝ) * (r - 1) ^ 2) • (fun n : ℕ => r ^ n) := by
    funext j
    simp [Pi.smul_apply]
  rw [hsecond, hconst, fwdDiff_iter_const_smul, hgeom]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsign :
      (-1 : ℝ) ^ k * (r - 1) ^ k = (19 / 20 : ℝ) ^ k := by
    dsimp [r]
    rw [show (20 : ℝ)⁻¹ - 1 = -(19 / 20 : ℝ) by norm_num]
    rw [← mul_pow]
    norm_num
  rw [show (-1 : ℝ) ^ k *
      ((1 / 20 : ℝ) * (r - 1) ^ 2 * ((r - 1) ^ k * r ^ n)) =
      ((-1 : ℝ) ^ k * (r - 1) ^ k) *
        ((1 / 20 : ℝ) * (r - 1) ^ 2 * r ^ n) by ring]
  rw [hsign]
  dsimp [r]
  positivity

end MathlibPlus.Analysis
