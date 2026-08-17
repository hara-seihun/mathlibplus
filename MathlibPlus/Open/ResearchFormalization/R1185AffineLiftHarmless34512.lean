import MathlibPlus.Open.Research.Q12PrimeCoverFormalization

namespace MathlibPlus.Open.ResearchFormalization.R1185AffineLiftHarmless34512

noncomputable section

/-- Claim 34512: every normalized affine lift of the forward switch is
ordinary-CI harmless on the explicit prime-cover carrier. -/
def claim34512 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (lam : MathlibPlus.Open.Research.Q12PrimeCover.Q12Carrier → (ZMod p)ˣ)
      (τ : MathlibPlus.Open.Research.Q12PrimeCover.Q12Carrier → ZMod p),
      lam MathlibPlus.Open.Research.Q12PrimeCover.q12One = 1 →
      τ MathlibPlus.Open.Research.Q12PrimeCover.q12One = 0 →
      ∀ S : Set (MathlibPlus.Open.Research.Q12PrimeCover.PrimeCoverCarrier p),
        MathlibPlus.Open.Research.Q12PrimeCover.gpInverseClosed p S →
        MathlibPlus.Open.Research.Q12PrimeCover.gpDerivativeInvariant p lam τ
          MathlibPlus.Open.Research.Q12PrimeCover.q12Switch
          MathlibPlus.Open.Research.Q12PrimeCover.q12SwitchInv S →
        ∃ α : MathlibPlus.Open.Research.Q12PrimeCover.PrimeCoverCarrier p →
            MathlibPlus.Open.Research.Q12PrimeCover.PrimeCoverCarrier p,
          MathlibPlus.Open.Research.Q12PrimeCover.gpAutomorphism p α ∧
            Set.image α S =
              Set.image
                (MathlibPlus.Open.Research.Q12PrimeCover.gpAffineLift p lam τ
                  MathlibPlus.Open.Research.Q12PrimeCover.q12Switch) S

end

end MathlibPlus.Open.ResearchFormalization.R1185AffineLiftHarmless34512
