import MathlibPlus.Open.ResearchBatch.R1542Claims

namespace MathlibPlus.Open.ResearchFormalization.R1542QuarticDerivative

open MathlibPlus.Open.ResearchBatch.R1542Claims

/-- Claim 37771: for each of the five slopes, the quartic translation has
zero dot product with the corresponding derivative direction after the
semidirect-product cocycle correction. -/
def claim37771_quarticDerivativeAnnihilationIdentity : Prop :=
  ∀ (p : ℕ), Nat.Prime p → p % 3 = 1 →
    ∀ (ω : ZMod p), scalarCubeRoot ω →
      ∀ (t : Fin 5) (k : H p),
        dot3 (nSlope t)
            (tau (hMul ω (hSlope ω t) k) -
              tau (hSlope ω t) - ω • tau k) = 0

end MathlibPlus.Open.ResearchFormalization.R1542QuarticDerivative
