import MathlibPlus.Open.ResearchFormalization.R1205.Claim32241

namespace MathlibPlus.Open.ResearchFormalization.R1205.Claim32240Repair

open MathlibPlus.Open.ResearchFormalization.R1205.Claim32241

noncomputable section

/-- Claim 32240: for the unique active chart supplied by the normalized
support-one carrier, the derivative from the `a⁻¹` section at vertex base `a`
lands at `j_q(a)` and has the exact displayed prime-fibre action. -/
def claim32240 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (Cp p))
      (f : Equiv.Perm (CpA4 p)),
      MathlibPlus.Open.ResearchFormalization.R1205SupportOne.normalizedSupportOneData p q σ f →
        ∀ a : A4, σ a ≠ 1 →
          ∀ y : ZMod p, ∀ x : Cp p,
            relativeDerivative p f
                (Multiplicative.ofAdd y, a⁻¹) (x, a) =
              (activeDerivativeWithBase p q σ a y x,
                transportedInversion q a)

end

end MathlibPlus.Open.ResearchFormalization.R1205.Claim32240Repair
