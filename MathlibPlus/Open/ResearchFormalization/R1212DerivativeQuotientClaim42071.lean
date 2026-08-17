import MathlibPlus.Open.ResearchFormalization.R1212

namespace MathlibPlus.Open.ResearchFormalization.R1212.DerivativeQuotient

/-- Claim 42071: in the exact one-nonlinear-chart profile, the quotient of
suitable target-fibre derivatives is conjugate to a nonzero translation, and
both the translation and its conjugate are full `p`-cycles. -/
def derivativeQuotientConjugateTranslation_claim42071 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (ZMod p))
      (f : Equiv.Perm (ProductGroup p)) (a h : A4) (t : ZMod p),
      normalizedCommonCoordinateMap q σ f →
      singletonNonlinearChart σ a →
      h ≠ 1 →
      σ (h * a) = MathlibPlus.Open.Research.translation p t →
      ∃ (y z c : ZMod p),
        c ≠ 0 ∧
        (y - (σ a) y) - (z - (σ a) z) = c ∧
        let r := targetBase q a h
        MathlibPlus.Open.ResearchFormalization.ProfileClaims.profileFiberDerivative
              σ a y r *
            (MathlibPlus.Open.ResearchFormalization.ProfileClaims.profileFiberDerivative
              σ a z r)⁻¹ =
          (σ r)⁻¹ * Equiv.addRight c * σ r ∧
        MathlibPlus.Open.Research.isFullCycle p (Equiv.addRight c) ∧
        MathlibPlus.Open.Research.isFullCycle p
          ((σ r)⁻¹ * Equiv.addRight c * σ r)

end MathlibPlus.Open.ResearchFormalization.R1212.DerivativeQuotient
