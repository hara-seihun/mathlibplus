import MathlibPlus.Open.ResearchFormalization.R1155Claim41415

namespace MathlibPlus.Open.ResearchFormalization.R1155Claim31651

open MathlibPlus.Open.ResearchFormalization.R1155C41415

noncomputable section

/-- Claim 31651: on the odd-factor times `C₂²` carrier, an extending
character is an automorphism shadow of the normalized Boolean switching on
all relative-derivative orbits. -/
def claim31651_characterShearDerivativeOrbitShadow : Prop :=
  ∀ (A : Type*) [AddCommGroup A] [Fintype A],
    Odd (Fintype.card A) →
    let H := A × (Boolean × Boolean)
    ∀ (κ : H → H → Boolean) (b : H → Boolean)
      (L : AddSubgroup H) (χ : H →+ Boolean),
      twistedExtensionLaw κ → b (0 : H) = 0 →
      (∀ h : H, h ∈ L ↔ h ∈ linearitySet b) →
      (∀ x y : L, b (x.1 + y.1) = b x.1 + b y.1) →
      (∀ h : L, χ h.1 = b h.1) →
      preservesTwistedLaw κ (characterShear χ) ∧
        (∀ h : H, ∀ e : Boolean,
          (h ∈ L →
            relativeDerivativeOrbit b (h, e) = singletonFiberOrbit h e) ∧
          (h ∉ L →
            relativeDerivativeOrbit b (h, e) = fullFiberOrbit h)) ∧
        (∀ x : TwistedCarrier H,
          Set.image (characterShear χ) (relativeDerivativeOrbit b x) =
            Set.image (booleanSwitch b) (relativeDerivativeOrbit b x))

end

end MathlibPlus.Open.ResearchFormalization.R1155Claim31651
