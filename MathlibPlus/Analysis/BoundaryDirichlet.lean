import Mathlib

namespace MathlibPlus.Analysis.BoundaryDirichlet

/-- The critical-line term has the claimed modulus, using the principal complex power. -/
theorem criticalLineTerm_norm (t : ℝ) (n : ℕ) :
    ‖(((n + 1 : ℕ) : ℝ) : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ =
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos]
  · norm_num
  · positivity

/-- The critical-line Dirichlet terms are not absolutely summable. -/
theorem criticalLine_not_absolutely_summable (t : ℝ) :
    ¬ Summable (fun n : ℕ =>
      ‖(((n + 1 : ℕ) : ℝ) : ℂ) ^ ((-(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) := by
  intro h
  have hshift : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
    exact h.congr (fun n => criticalLineTerm_norm t n)
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    apply (summable_nat_add_iff (G := ℝ) 1).mp
    simpa [Nat.cast_add] using hshift
  have hp : (-(1 / 2 : ℝ)) < -1 := (Real.summable_nat_rpow.mp hbase)
  norm_num at hp

end MathlibPlus.Analysis.BoundaryDirichlet
