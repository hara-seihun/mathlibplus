import Mathlib

namespace MathlibPlus.Logic.Claim42301

/-- Claim 42301: feasibility at a cap alone does not logically certify that
all smaller caps are infeasible. -/
theorem capFeasibilityDoesNotImplyMinimum_claim42301 :
    ¬ (∀ (Feasible : ℕ → Prop), Feasible 40 →
      ∀ n : ℕ, n < 40 → ¬ Feasible n) := by
  intro h
  have hbad := h (fun _ : ℕ => True) trivial 0 (by omega)
  exact hbad trivial

end MathlibPlus.Logic.Claim42301
