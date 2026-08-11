import MathlibPlus.Analysis.ThetaMellin

namespace MathlibPlus.Analysis.ThetaMellin

/-- The expanded positive-index theta shell from admitted claim 4660. -/
theorem thetaShell_eq_claim4660 (m : ℕ) (_hm : 1 ≤ m) (u : ℝ) :
    thetaShell m u =
      Real.exp (u / 2) *
        (4 * (Real.pi * (m : ℝ) ^ 2) ^ 2 * Real.exp (4 * u) -
          6 * (Real.pi * (m : ℝ) ^ 2) * Real.exp (2 * u)) *
        Real.exp (-(Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u))) := by
  have hexp9 : Real.exp (9 * u / 2) =
      Real.exp (u / 2) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp5 : Real.exp (5 * u / 2) =
      Real.exp (u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [thetaShell, hexp9, hexp5]
  ring_nf

/-- The `h`-profile form of the centered theta shell from admitted claim 11216. -/
theorem thetaShell_eq_claim11216 (n : ℕ) (_hn : 1 ≤ n) (u : ℝ) :
    thetaShell n u =
      Real.exp (u / 2) *
        ((4 * (Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
            6 * (Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
          Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)))) := by
  have hexp9 : Real.exp (9 * u / 2) =
      Real.exp (u / 2) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp5 : Real.exp (5 * u / 2) =
      Real.exp (u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp4 : Real.exp (2 * u) ^ 2 = Real.exp (4 * u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [thetaShell, hexp9, hexp5]
  rw [show (Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 =
      (Real.pi * (n : ℝ) ^ 2) ^ 2 * Real.exp (2 * u) ^ 2 by ring]
  rw [hexp4]
  ring_nf

end MathlibPlus.Analysis.ThetaMellin
