import MathlibPlus.Analysis.ThetaMellin
import MathlibPlus.Analysis.ThetaShell

namespace MathlibPlus.Analysis

/-- The positive-index completed-theta shell from claim 3181 is strictly
positive on the source half-line. The later assertions about the infinite
source, Schwartz regularity, and the operator are separate analytic claims. -/
theorem thetaShell_pos_claim3181 (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 ≤ u) :
    0 < ThetaMellin.thetaShell n u := by
  rw [ThetaMellin.thetaShell_eq_factored]
  exact ThetaShell.strictPos n hn u hu

end MathlibPlus.Analysis
