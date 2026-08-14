import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace MathlibPlus.Open.Research.AdmittedBatchR0148

/-- The order-two complement identity for Möbius signs on squarefree divisors. -/
def even_order_mobius_sign_invariance : Prop :=
  ∀ R_P d₁ d₂ : ℕ,
    Squarefree R_P → d₁ ∣ R_P → d₂ ∣ R_P →
      ArithmeticFunction.moebius (R_P / d₁) *
          ArithmeticFunction.moebius (R_P / d₂) =
        ArithmeticFunction.moebius d₁ * ArithmeticFunction.moebius d₂

end MathlibPlus.Open.Research.AdmittedBatchR0148
