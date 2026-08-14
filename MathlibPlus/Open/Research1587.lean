import Mathlib

namespace MathlibPlus.Open.Research1587

/-- The source derivative function appearing in Record 1. -/
def sourceDerivative {A : Type*} [AddGroup A]
    (h : A ≃ A) (k : A) : A → A :=
  fun z => h.symm (h (z + k) - h k)

/-- The edge voltage appearing in Record 1. -/
def edgeVoltage {A R : Type*} [AddGroup A] [AddGroup R]
    (h : A ≃ A) (f : A → R) (k z : A) : R :=
  f (z + k) - f k - f (sourceDerivative h k z)

/-- Claim 37914. -/
def sourceDerivativeAndEdgeVoltage_claim37914 : Prop :=
  ∀ (A R : Type*) [AddGroup A] [AddGroup R]
    (h : A ≃ A) (f : A → R) (k : A),
    Function.Bijective (sourceDerivative h k) ∧
      ∀ z : A,
        edgeVoltage h f k z =
          f (z + k) - f k - f (h.symm (h (z + k) - h k))

end MathlibPlus.Open.Research1587
