import Mathlib

namespace MathlibPlus.Analysis.Claim2308

/-- The finite arithmetic kernel from claim 2308, with the strict cutoff
written as a finite filtered sum. -/
noncomputable def arithmeticKernel (c : ℕ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sqrt (c : ℝ) *
    ∑ n ∈ ((Finset.Icc 1 (c - 1)).filter
      (fun n : ℕ => (n : ℝ) < (c : ℝ) * Real.exp (-x))),
      p ((n : ℝ) * Real.exp x / (c : ℝ))

/-- The value jump at the cutoff where the summand with argument one
 disappears. -/
noncomputable def internalValueJump (p : ℝ → ℝ) (n : ℕ) : ℝ :=
  p 1 / Real.sqrt (n : ℝ)

/-- Exact endpoint values, including the endpoint-flatness hypothesis from the
claim.  The hypothesis `p 1 = 0` is used by the jump statement below; it is
retained here because the source claim states the two endpoint facts together
under that hypothesis. -/
theorem endpointValues (c : ℕ) (hc : 0 < c) (p : ℝ → ℝ) (hp : p 1 = 0) :
    arithmeticKernel c p (Real.log c) = 0 ∧
      arithmeticKernel c p 0 =
        (1 / Real.sqrt (c : ℝ)) *
          ∑ n ∈ Finset.Icc 1 (c - 1), p ((n : ℝ) / (c : ℝ)) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hleft :
      ((Finset.Icc 1 (c - 1)).filter
          (fun n : ℕ => (n : ℝ) < (c : ℝ) * Real.exp (- (0 : ℝ)))) =
        Finset.Icc 1 (c - 1) := by
    apply Finset.filter_eq_self.mpr
    intro n hn
    have hnle : n ≤ c - 1 := (Finset.mem_Icc.mp hn).2
    have hnc : n < c := by omega
    simpa [Real.exp_zero] using (show (n : ℝ) < (c : ℝ) by exact_mod_cast hnc)
  have hlogexp : Real.exp (-Real.log (c : ℝ)) = 1 / (c : ℝ) := by
    rw [Real.exp_neg, Real.exp_log hcR]
    exact (one_div (c : ℝ)).symm
  have hlogprod : (c : ℝ) * Real.exp (-Real.log (c : ℝ)) = 1 := by
    rw [hlogexp]
    field_simp
  have hright :
      ((Finset.Icc 1 (c - 1)).filter
          (fun n : ℕ => (n : ℝ) < (c : ℝ) * Real.exp (-Real.log (c : ℝ)))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn
    have hnlo : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [hlogprod]
    exact_mod_cast (not_lt_of_ge hnlo)
  constructor
  · unfold arithmeticKernel
    rw [hright]
    simp
  · unfold arithmeticKernel
    rw [hleft]
    simp [div_eq_mul_inv]

/-- If the source vanishes at one, every internal value-jump symbol vanishes. -/
theorem internalValueJump_eq_zero (p : ℝ → ℝ) (hp : p 1 = 0) (n : ℕ) :
    internalValueJump p n = 0 := by
  simp [internalValueJump, hp]

end MathlibPlus.Analysis.Claim2308
