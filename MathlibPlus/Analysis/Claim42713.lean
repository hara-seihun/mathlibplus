import Mathlib

namespace MathlibPlus.Analysis.Claim42713

/-- Claim 42713: polarization gives the exact increment of the squared energy. -/
theorem energyIncrement_claim42713 {E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ℕ → E) :
    ∀ N : ℕ, 1 < N →
      ‖u N‖ ^ 2 - ‖u (N - 1)‖ ^ 2 =
        2 * inner ℝ (u (N - 1)) (u N - u (N - 1)) +
          ‖u N - u (N - 1)‖ ^ 2 := by
  intro N hN
  have hdecomp : u N = u (N - 1) + (u N - u (N - 1)) := by
    abel
  calc
    ‖u N‖ ^ 2 - ‖u (N - 1)‖ ^ 2 =
        ‖u (N - 1) + (u N - u (N - 1))‖ ^ 2 -
          ‖u (N - 1)‖ ^ 2 := by rw [← hdecomp]
    _ = 2 * inner ℝ (u (N - 1)) (u N - u (N - 1)) +
          ‖u N - u (N - 1)‖ ^ 2 := by
      rw [norm_add_sq_real]
      ring

end MathlibPlus.Analysis.Claim42713
