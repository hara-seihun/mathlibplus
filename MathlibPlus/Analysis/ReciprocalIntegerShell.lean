import MathlibPlus.Basic

namespace MathlibPlus.Analysis.ReciprocalIntegerShell

/--
No fixed positive integer label can realize the reciprocal reflection for all
real scales.  The shell labels are positive naturals and the scale parameter is
quantified over all real `u`, exactly as in the admitted claim.
-/
theorem noFixedReciprocalIntegerShellPartner :
    ∀ n : ℕ, 0 < n →
      ¬ ∃ m : ℕ, 0 < m ∧
        ∀ u : ℝ,
          (m : ℝ)^2 * Real.exp (2 * u) =
            (n : ℝ)^2 * Real.exp (-2 * u) := by
  intro n hn h
  rcases h with ⟨m, _hm, hEq⟩
  have h0 := hEq 0
  have h1 := hEq 1
  norm_num at h0 h1
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsq : (m : ℝ)^2 = (n : ℝ)^2 := by
    rw [h0]
  rw [hsq] at h1
  have hn2 : (n : ℝ)^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hnR)
  have hexp : Real.exp (2 : ℝ) = Real.exp (-2 : ℝ) :=
    mul_left_cancel₀ hn2 h1
  have hlt : Real.exp (-2 : ℝ) < Real.exp (2 : ℝ) := by
    exact Real.exp_lt_exp.mpr (by norm_num)
  exact (ne_of_gt hlt) hexp

end MathlibPlus.Analysis.ReciprocalIntegerShell
