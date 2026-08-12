import MathlibPlus.Analysis.ReciprocalXi

namespace MathlibPlus.NumberTheory.Claim14275

/--
The arithmetic core of claim 14275: two nontrivial xi zeros in the critical
strip cannot collide after distinct even integral shifts.  The zero condition
is explicit; the proof uses only the displayed critical-strip bounds.
-/
theorem distinctEvenShifts
    {ρ ρ' : ℂ} {m n : ℤ}
    (hξ : MathlibPlus.Analysis.ReciprocalXi.xi ρ = 0)
    (hξ' : MathlibPlus.Analysis.ReciprocalXi.xi ρ' = 0)
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (hρ'₀ : 0 < ρ'.re) (hρ'₁ : ρ'.re < 1)
    (h : (2 : ℂ) * m + ρ = (2 : ℂ) * n + ρ') :
    m = n ∧ ρ = ρ' := by
  have hreal : (2 : ℝ) * m + ρ.re = (2 : ℝ) * n + ρ'.re := by
    simpa using congrArg Complex.re h
  have hmn : m = n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hcast : (m : ℝ) + 1 ≤ n := by
        have hstep : m + 1 ≤ n := by omega
        exact_mod_cast hstep
      nlinarith
    · have hcast : (n : ℝ) + 1 ≤ m := by
        have hstep : n + 1 ≤ m := by omega
        exact_mod_cast hstep
      nlinarith
  refine ⟨hmn, ?_⟩
  subst n
  simpa using h

end MathlibPlus.NumberTheory.Claim14275
