import MathlibPlus.Open.ResearchFormalization.R1441MarkedOffsetTransport

namespace MathlibPlus.Open.ResearchFormalization.R1441DerivativeOrbits

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1441MarkedOffsetTransport

/-- The translation generator in quotient row `h` indexed by `k`. -/
def derivativeGenerator (τ : H → W) (h k : H) : W :=
  τ (hMul h k) - τ h - hScalar h (τ k)

/-- The normalization at the quotient identity for `τ`. -/
def normalizedTau (τ : H → W) : Prop :=
  τ (0, 0) = 0

/-- The pure-translation profile attached to `τ`. -/
def pureTranslationProfile (τ : H → W) : H → Equiv.Perm W :=
  fun h => Equiv.addRight (τ h)

/-- The `F₇`-span of the normalized derivative translations in row `h`. -/
def derivativeSubspace (τ : H → W) (h : H) : Submodule (ZMod 7) W :=
  Submodule.span (ZMod 7) (Set.range (fun k => derivativeGenerator τ h k))

/-- The affine coset of the derivative span through `w`. -/
def derivativeCoset (τ : H → W) (h : H) (w : W) : Set W :=
  Set.image (fun d : W => w + d) (derivativeSubspace τ h : Set W)

/-- Claim 37223: for the exact `H = E(C₇,3)` and `W = F₇²` carrier, the
pure-translation normalized relative derivatives are translations by the
stated generators, and their orbits are exactly the affine cosets of `D_h`. -/
def claim37223 : Prop :=
  ∀ (τ : H → W),
    normalizedTau τ →
    ∀ (h : H) (w : W),
    (∀ (k : H) (x : W),
      normalizedRelativeDerivative (pureTranslationProfile τ) h k x =
        Equiv.addRight (derivativeGenerator τ h k)) ∧
    derivativeOrbit (pureTranslationProfile τ) h w =
      derivativeCoset τ h w

end
end MathlibPlus.Open.ResearchFormalization.R1441DerivativeOrbits
