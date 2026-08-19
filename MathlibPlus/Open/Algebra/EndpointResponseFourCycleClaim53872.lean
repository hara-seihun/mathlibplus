import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 53872: every antisymmetric endpoint response cancels on the
specified opposite-endpoint four-cycle, with no extra algebraic structure. -/
def antisymmetricEndpointFourCycle_claim53872 : Prop :=
  ∀ {P X Z : Type*} [AddCommGroup Z]
    (q : P → X) (φ : X → X → Z),
    (∀ x y, φ y x = -φ x y) →
      (∀ x, φ x x = 0) →
        ∀ A B D C : P, q A = q D →
          φ (q A) (q B) + φ (q B) (q D) +
              φ (q D) (q C) + φ (q C) (q A) = 0

end MathlibPlus.Open.Algebra
