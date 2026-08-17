import MathlibPlus.Open.ResearchFormalization.R0100LaguerreFlags

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0100Claim17937

noncomputable section

/-- The positive-particle Laguerre theta sum, written with the actual
recurrence-defined generalized Laguerre carrier. -/
def claim17937 : Prop :=
  ∀ (n : ℕ) (α y : ℝ),
    MathlibPlus.Open.ResearchFormalization.R0100LaguerreFlags.exponentialLaguerreTheta
        n α y =
      ∑' m : {m : ℕ // 1 ≤ m},
        Real.exp (-Real.pi * (m.1 : ℝ) ^ 2 * y) *
          (MathlibPlus.Open.NewResearch2.ModularLaguerre.generalizedLaguerre n α).eval
            (Real.pi * (m.1 : ℝ) ^ 2 * y)

end

end MathlibPlus.Open.ResearchFormalization.R0100Claim17937
