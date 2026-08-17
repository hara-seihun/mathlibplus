import MathlibPlus.Open.Research.Q12PrimeCoverFormalization

namespace MathlibPlus.Open.ResearchFormalization.R1185FullStabilizer41759

open MathlibPlus.Open.Research.Q12PrimeCover

noncomputable section

/-- The affine unit forced by the parity character and the forward switch. -/
def affineUnitRatio (p : ℕ) (h : Q12Carrier) : (ZMod p)ˣ :=
  q12ChiUnit p (q12Switch h) / q12ChiUnit p h

/-- Claim 41759: a normalized scalar profile with full stabilizer has the
literal parity-character ratio at every element of `Q₁₂`. -/
def claim41759 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ lam : Q12Carrier → (ZMod p)ˣ,
      lam q12One = 1 →
        q12ScalarStabilizer p lam q12Switch =
            (Set.univ : Set Q12Carrier) →
          ∀ h : Q12Carrier, lam h = affineUnitRatio p h

end

end MathlibPlus.Open.ResearchFormalization.R1185FullStabilizer41759
