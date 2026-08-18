import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0034Claims17371_17372

namespace MathlibPlus.Open.ResearchFormalization.Claim17369

open MeasureTheory
open scoped BigOperators
open MathlibPlus.Open.NewResearch2.R0033
open MathlibPlus.Open.ResearchFormalization.R0034Claims17371_17372

noncomputable section

/-- Claim 17369: the factorial-scaled modular-Laguerre coefficient is the
    moment of x+y for the exact theta and Gamma measures. -/
def claim17369_modular_laguerre_moment_representation : Prop :=
  ∀ α : ℝ, -((1 : ℝ) / 2) ≤ α →
    ∀ n : ℕ,
      (Nat.factorial n : ℝ) * laguerreCoefficient α n =
        ∫ x : ℝ, ∫ y : ℝ,
          (x + y) ^ n
          ∂(gammaMeasure (α + (1 : ℝ) / 2)) ∂thetaMeasure

end

end MathlibPlus.Open.ResearchFormalization.Claim17369
