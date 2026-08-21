-- UNVERIFIED (does-not-elaborate): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim7365

/-- The signed maximal-cofactor vector of a full-row-rank rectangular matrix is
in its right kernel, with the final coordinate normalized to one. -/
theorem signedMaximalCofactorKernelVector_claim7365
    {n : ℕ} (R : Matrix (Fin n) (Fin n.succ) ℝ)
    (_hR : Matrix.rank R = n)
    (hΔ : (R.submatrix id (Fin.succAbove (Fin.last n))).det ≠ 0) :
    let Δ : Fin n.succ → ℝ := fun j =>
      (R.submatrix id (Fin.succAbove j)).det
    let q : Fin n.succ → ℝ := fun j =>
      (-1 : ℝ) ^ (n - j.1) * Δ j / Δ (Fin.last n)
    q (Fin.last n) = 1 ∧ Matrix.mulVec R q = 0 := by
  let Δ : Fin n.succ → ℝ := fun j =>
    (R.submatrix id (Fin.succAbove j)).det
  let q : Fin n.succ → ℝ := fun j =>
    (-1 : ℝ) ^ (n - j.1) * Δ j / Δ (Fin.last n)
  have hΔlast : Δ (Fin.last n) ≠ 0 := by
    simpa [Δ] using hΔ
  have hkernel (i : Fin n) :
      ∑ j : Fin n.succ, (-1 : ℝ) ^ (n - j.1) * R i j * Δ j = 0 := by
    let A : Matrix (Fin n.succ) (Fin n.succ) ℝ := fun a b =>
      Fin.cases (R i b) (fun k => R k b) a
    have hA : A.det = 0 := by
      apply Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i).symm
      funext b
      simp [A]
    have hexp := Matrix.det_succ_row_zero A
    rw [hA] at hexp
    have hexp' :
        ∑ j : Fin n.succ, (-1 : ℝ) ^ j.1 * R i j * Δ j = 0 := by
      simpa [A, Δ, Matrix.submatrix] using hexp.symm
    have hsum :
        ∑ j : Fin n.succ, R i j *
            ((-1 : ℝ) ^ (n - j.1) * Δ j) = 0 := by
      calc
        _ = ∑ j : Fin n.succ,
            (-1 : ℝ) ^ n * ((-1 : ℝ) ^ j.1 * R i j * Δ j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjle : j.1 ≤ n := Nat.le_of_lt_succ j.isLt
          have hsign : (-1 : ℝ) ^ (n - j.1) =
              (-1 : ℝ) ^ n * (-1 : ℝ) ^ j.1 := by
            calc
              (-1 : ℝ) ^ (n - j.1) =
                  (-1 : ℝ) ^ (n - j.1) *
                    ((-1 : ℝ) ^ j.1 * (-1 : ℝ) ^ j.1) := by
                have hsq : (-1 : ℝ) ^ j.1 * (-1 : ℝ) ^ j.1 = 1 := by
                  rw [← pow_add]
                  have : j.1 + j.1 = 2 * j.1 := by omega
                  rw [this, pow_mul]
                  norm_num
                rw [hsq, mul_one]
              _ = ((-1 : ℝ) ^ (n - j.1) * (-1 : ℝ) ^ j.1) *
                    (-1 : ℝ) ^ j.1 := by ring
              _ = (-1 : ℝ) ^ n * (-1 : ℝ) ^ j.1 := by
                rw [← pow_add, Nat.sub_add_cancel hjle]
          rw [hsign]
          ring
        _ = (-1 : ℝ) ^ n *
              ∑ j : Fin n.succ, (-1 : ℝ) ^ j.1 * R i j * Δ j := by
          rw [Finset.mul_sum]
        _ = 0 := by rw [hexp'] ; ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  constructor
  · dsimp [q, Δ]
    have hpow : (-1 : ℝ) ^ (n - n) = 1 := by simp
    rw [hpow, one_mul]
    exact div_self hΔ
  · funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    calc
      (∑ j : Fin n.succ, R i j * q j) =
          ∑ j : Fin n.succ,
            (R i j * ((-1 : ℝ) ^ (n - j.1) * Δ j)) /
              Δ (Fin.last n) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [q]
        ring
      _ = (∑ j : Fin n.succ,
            R i j * ((-1 : ℝ) ^ (n - j.1) * Δ j)) /
              Δ (Fin.last n) := by rw [Finset.sum_div]
      _ = 0 := by
