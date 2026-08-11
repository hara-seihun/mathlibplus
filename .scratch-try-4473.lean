import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory.Claim4473

 theorem arithmeticUnitPhase (x : ℝ) (n : ℕ) (hn : 0 < n) :
    Complex.exp (Complex.I * (x : ℂ) * (Real.log (n : ℝ) : ℂ)) =
      (n : ℂ) ^ (Complex.I * (x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero]
  · rw [← Complex.ofReal_log (show (0 : ℝ) ≤ n by exact_mod_cast (Nat.zero_le n))]
    norm_num
    ring_nf
  · exact_mod_cast (Nat.ne_of_gt hn)

end MathlibPlus.NumberTheory.Claim4473
