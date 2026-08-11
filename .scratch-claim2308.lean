import Mathlib

namespace Test2308

noncomputable def arithmeticKernel (c : ℕ) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sqrt (c : ℝ) *
    ∑ n in (Finset.Icc 1 (c - 1)).filter
      (fun n => (n : ℝ) < (c : ℝ) * Real.exp (-x)),
      p ((n : ℝ) * Real.exp x / (c : ℝ))

def internalValueJump (p : ℝ → ℝ) (n : ℕ) : ℝ := p 1 / Real.sqrt (n : ℝ)

theorem endpointValues (c : ℕ) (hc : 0 < c) (p : ℝ → ℝ) (hp : p 1 = 0) :
    arithmeticKernel c p (Real.log c) = 0 ∧
      arithmeticKernel c p 0 =
        (1 / Real.sqrt (c : ℝ)) *
          ∑ n in Finset.Icc 1 (c - 1), p ((n : ℝ) / (c : ℝ)) := by
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hleft :
      (Finset.Icc 1 (c - 1)).filter
          (fun n => (n : ℝ) < (c : ℝ) * Real.exp (- (0 : ℝ))) =
        Finset.Icc 1 (c - 1) := by
    apply Finset.filter_eq_self.mpr
    intro n hn
    have hnle : n ≤ c - 1 := (Finset.mem_Icc.mp hn).2
    have hnc : n < c := by omega
    simpa [Real.exp_zero] using (show (n : ℝ) < (c : ℝ) by exact_mod_cast hnc)
  have hlogexp : Real.exp (-Real.log (c : ℝ)) = 1 / (c : ℝ) := by
    rw [Real.exp_neg, Real.exp_log hcR]
  have hlogprod : (c : ℝ) * Real.exp (-Real.log (c : ℝ)) = 1 := by
    rw [hlogexp]
    field_simp
  have hright :
      (Finset.Icc 1 (c - 1)).filter
          (fun n => (n : ℝ) < (c : ℝ) * Real.exp (-Real.log (c : ℝ))) = ∅ := by
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
    congr 1
    simp [div_eq_mul_inv]

 theorem jump_zero (p : ℝ → ℝ) (hp : p 1 = 0) (n : ℕ) :
    internalValueJump p n = 0 := by
  simp [internalValueJump, hp]

end Test2308
