import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 12224: distinct closed-prime fibres have zero tensor product, while
identical prime fibres tensor back to the residue field. -/
def distinctClosedPrimeFiberProducts : Prop :=
  (∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p ≠ q →
      ∀ x : TensorProduct ℤ (ZMod p) (ZMod q), x = 0) ∧
    (∀ (p : ℕ), Nat.Prime p →
      Nonempty (TensorProduct ℤ (ZMod p) (ZMod p) ≃ₐ[ℤ] ZMod p))

end MathlibPlus.Open.Algebra
