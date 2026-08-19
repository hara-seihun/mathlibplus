import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 5999: a nowhere-zero affine scalar on a nonzero finite-dimensional
`𝔽_p`-vector space has zero linear part and nonzero constant part. -/
def nowhereZeroAffineScalar_5999 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [AddCommGroup H] [Module (ZMod p) H]
    [FiniteDimensional (ZMod p) H] [Nontrivial H]
    (ell : H →ₗ[ZMod p] ZMod p) (c : ZMod p),
    (∀ x : H, ell x + c ≠ 0) →
      ell = 0 ∧ c ≠ 0

end MathlibPlus.LinearAlgebra
