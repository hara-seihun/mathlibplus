import MathlibPlus.Open.ResearchBatch.R1542Claims

namespace MathlibPlus.Open.ResearchFormalization.R1542UniformQuartic

noncomputable section

open MathlibPlus.Open.ResearchBatch.R1542Claims

/-- Claim 37766: on the exact scalar `E(C_p^4,3)` carrier, the five
slope vectors, perpendicular planes, quartic translation, and normalized
bijection have the displayed formulas. -/
def claim37766_uniformQuarticTranslationAndPlanes : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 3 = 1 →
    ∀ ω : ZMod p, scalarCubeRoot ω →
      (∀ t : Fin 5,
        hSlope ω t = ((1 - ω) * slopeValue t, (1 : ZMod 3)) ∧
        nSlope t = ![(1 : ZMod p), slopeValue t, (slopeValue t) ^ 2] ∧
        plane ω t =
          {w : W p | dot3 (nSlope t) w = 0}) ∧
      Function.Bijective (normalizedBijection (p := p)) ∧
      (∀ h : H p,
        tau h = ![h.1 ^ 4, -4 * h.1 ^ 3, 6 * h.1 ^ 2]) ∧
      (∀ w : W p, ∀ h : H p,
        normalizedBijection (w, h) = (w + tau h, h))

end

end MathlibPlus.Open.ResearchFormalization.R1542UniformQuartic
