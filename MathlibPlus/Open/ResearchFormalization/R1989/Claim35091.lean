import MathlibPlus.Open.ResearchFormalization.GrowingOrbitTheoremClaim35101

namespace MathlibPlus.Open.ResearchFormalization.R1989

open MathlibPlus.Open.ResearchFormalization.GrowingOrbitTheoremClaim35101

/-- Claim 35091: under the coefficient-one-quarter eventual orbit cap, every
C4-free directional family has the stated upper density and edge bounds. -/
def claim35091 : Prop :=
  ∀ (M : ℕ → ℕ) (f : DirectionalFamily),
    eventualOrbitBound M (3 / 4 : ℝ) →
      familyC4Free f →
        familyOrbitCapped f M →
          densityUpperAsymptotic f ∧ edgeUpperAsymptotic f

end MathlibPlus.Open.ResearchFormalization.R1989
