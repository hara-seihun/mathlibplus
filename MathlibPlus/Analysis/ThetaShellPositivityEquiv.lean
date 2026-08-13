import MathlibPlus.Analysis.ThetaShell
import MathlibPlus.Open.Analysis.ThetaShell
import MathlibPlus.Open.Analysis.ThetaSourcePositivityClaim19068

open scoped BigOperators

namespace MathlibPlus.Analysis.ThetaShell

private theorem shell_eq_two_mul_source (m : ℕ) (v : ℝ) :
    2 * Real.pi * (m : ℝ) ^ 2 * Real.exp (5 * v / 2) *
        (2 * Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * v) - 3) *
        Real.exp (-Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * v)) =
      2 * MathlibPlus.Analysis.thetaShellSummand m (v / 2) := by
  have h9 : Real.exp (9 * (v / 2)) =
      Real.exp (5 * v / 2) * Real.exp (2 * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h5 : Real.exp (5 * (v / 2)) = Real.exp (5 * v / 2) := by
    congr 1
    ring
  have h4 : Real.exp (4 * (v / 2)) = Real.exp (2 * v) := by
    congr 1
    ring
  rw [MathlibPlus.Analysis.thetaShellSummand, h9, h5, h4]
  ring

private theorem shell_tsum_eq_two_mul_source_tsum (v : ℝ) :
    (∑' n : ℕ,
      2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * v / 2) *
        (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v) - 3) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * v))) =
      2 * ∑' m : {m : ℕ // 0 < m},
        MathlibPlus.Analysis.thetaShellSummand m.1 (v / 2) := by
  calc
    _ = ∑' n : ℕ,
        2 * MathlibPlus.Analysis.thetaShellSummand (n + 1) (v / 2) := by
          apply tsum_congr
          intro n
          exact shell_eq_two_mul_source (n + 1) v
    _ = 2 * ∑' n : ℕ,
        MathlibPlus.Analysis.thetaShellSummand (n + 1) (v / 2) := tsum_mul_left
    _ = 2 * ∑' m : {m : ℕ // 0 < m},
        MathlibPlus.Analysis.thetaShellSummand m.1 (v / 2) := by
          congr 1
          exact (tsum_pnat_eq_tsum_succ
            (f := fun m : ℕ =>
              MathlibPlus.Analysis.thetaShellSummand m (v / 2))).symm

/-- Claim 342 and claim 19068 are the same total theta-shell positivity assertion
under `v = 2u`; the extra pointwise clauses in claim 342 are unconditional. -/
theorem strictPositivity_iff_thetaSourcePositivity_claim19068 :
    MathlibPlus.Open.Analysis.ThetaShell.strictPositivity ↔
      MathlibPlus.Open.Analysis.thetaSourcePositivity_claim19068 := by
  unfold MathlibPlus.Open.Analysis.ThetaShell.strictPositivity
    MathlibPlus.Open.Analysis.thetaSourcePositivity_claim19068
  constructor
  · rintro ⟨_, hsum⟩ u hu
    have h := hsum (2 * u) (by linarith)
    rw [shell_tsum_eq_two_mul_source_tsum] at h
    have huv : (2 * u) / 2 = u := by ring
    rw [huv] at h
    nlinarith
  · intro hsource
    constructor
    · intro u n hu hn
      refine ⟨by nlinarith [Real.pi_gt_three], ?_, strictPos n hn u hu⟩
      have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn_sq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have hexp : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
      have hprod : (1 : ℝ) ≤ (n : ℝ) ^ 2 * Real.exp (2 * u) :=
        one_le_mul_of_one_le_of_one_le hn_sq hexp
      have hscaled : 2 * Real.pi * 1 ≤
          2 * Real.pi * ((n : ℝ) ^ 2 * Real.exp (2 * u)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      nlinarith
    · intro v hv
      have h := hsource (v / 2) (by linarith)
      rw [shell_tsum_eq_two_mul_source_tsum]
      exact mul_pos (by norm_num) h

end MathlibPlus.Analysis.ThetaShell
