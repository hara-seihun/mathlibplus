import MathlibPlus.Open.ResearchFormalization.R1212

namespace MathlibPlus.Open.ResearchFormalization.R1212RelativeDerivative

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1212

/-- Claim 42069: the exact target-fibre relative derivative formula at the
unique nonlinear base. -/
def claim42069_relativeDerivativeTargetFiber : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (ZMod p))
      (f : Equiv.Perm (ProductGroup p)) (a h : A4) (t : ZMod p),
      normalizedCommonCoordinateMap q σ f →
      singletonNonlinearChart σ a →
      h ≠ 1 →
      σ (h * a) = MathlibPlus.Open.Research.translation p t →
      ∀ (x y : ZMod p),
        targetFiberDerivativeValue f a h y x =
          (σ (targetBase q a h)).symm
            (x + y + t - (σ a) y)

end

end MathlibPlus.Open.ResearchFormalization.R1212RelativeDerivative
