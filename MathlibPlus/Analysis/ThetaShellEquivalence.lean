import MathlibPlus.Open.Analysis.ThetaShell
import MathlibPlus.Open.Analysis.ThetaSourcePositivityClaim19068
import MathlibPlus.Analysis.ThetaShell
import MathlibPlus.Analysis.ThetaShellSummandClaim19068

open scoped BigOperators

namespace MathlibPlus.Analysis.ThetaShell

private lemma shell_eq_twice_source (n : ℕ) (u : ℝ) :
    2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * (2 * u) / 2) *
        (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * (2 * u)) - 3) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * (2 * u))) =
      2 * MathlibPlus.Analysis.thetaShellSummand (n + 1) u := by
  dsimp [MathlibPlus.Analysis.thetaShellSummand]
  rw [show Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) by
    rw [← Real.exp_add]
    congr 1 <;> ring]
  ring

private lemma shell_tsum_eq_twice_source_tsum (u : ℝ) :
    (∑' n : ℕ,
      2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * (2 * u) / 2) *
        (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * (2 * u)) - 3) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * (2 * u)))) =
      2 * (∑' m : {m : ℕ // 0 < m},
        MathlibPlus.Analysis.thetaShellSummand m.1 u) := by
  rw [show (∑' n : ℕ,
      2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * (2 * u) / 2) *
        (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * (2 * u)) - 3) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * (2 * u)))) =
      ∑' n : ℕ, 2 * MathlibPlus.Analysis.thetaShellSummand (n + 1) u by
    congr 1
    funext n
    exact shell_eq_twice_source n u]
  rw [← tsum_mul_left]
  exact (tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ => 2 * MathlibPlus.Analysis.thetaShellSummand n u)).symm

/-- The theta-shell positivity node and the source-level positive-index sum are
    equivalent after the exact dilation `v = 2u`. -/
theorem strictPositivity_iff_thetaSourcePositivity_claim19068 :
    MathlibPlus.Open.Analysis.ThetaShell.strictPositivity ↔
      MathlibPlus.Open.Analysis.thetaSourcePositivity_claim19068 := by
  constructor
  · intro h u hu
    have hsum := h.2 (2 * u) (by linarith)
    rw [shell_tsum_eq_twice_source_tsum u] at hsum
    nlinarith
  · intro h
    constructor
    · intro u n hu hn
      have hstrict := MathlibPlus.Analysis.ThetaShell.strictPos n hn u hu
      have hn_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn_sq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have hexp : (1 : ℝ) ≤ Real.exp (2 * u) :=
        Real.one_le_exp (by linarith)
      have hprod : (1 : ℝ) ≤ (n : ℝ) ^ 2 * Real.exp (2 * u) := by
        exact one_le_mul_of_one_le_of_one_le hn_sq hexp
      have hpi_prod : 2 * Real.pi ≤
          2 * Real.pi * ((n : ℝ) ^ 2 * Real.exp (2 * u)) := by
        have hnonneg : 0 ≤
            (2 * Real.pi) * ((n : ℝ) ^ 2 * Real.exp (2 * u) - 1) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr hprod)
        nlinarith
      have hmiddle : 2 * Real.pi - 3 ≤
          2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3 := by
        nlinarith
      have hpi : 0 < 2 * Real.pi - 3 := by
        nlinarith [Real.pi_gt_three]
      exact ⟨hpi, hmiddle, hstrict⟩
    · intro u hu
      have hsource := h (u / 2) (by linarith)
      have hsum := shell_tsum_eq_twice_source_tsum (u / 2)
      have hu' : 2 * (u / 2) = u := by ring
      rw [hu'] at hsum
      rw [hsum]
      nlinarith

end MathlibPlus.Analysis.ThetaShell
