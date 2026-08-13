import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim11326

/-- The three square-port combinations have the displayed affine identities.
The theorem is purely algebraic, so it is stated over an arbitrary
commutative ring. -/
theorem squarePortIdentities
    {R : Type _} [CommRing R] (r H H₁ H₂ : R) :
    let S₀ := H₂
    let S₁ := -H₂ - 2 * r * H₁
    let S₂ := H₂ + 4 * r * H₁ + 4 * r ^ 2 * H
    S₀ + 2 * S₁ + S₂ = 4 * r ^ 2 * H ∧
      S₂ - S₀ = 4 * r * (H₁ + r * H) ∧
      S₀ * S₂ - S₁ ^ 2 = 4 * r ^ 2 * (H * H₂ - H₁ ^ 2) := by
  dsimp
  constructor
  · ring
  constructor
  · ring
  · ring

end MathlibPlus.Algebra.Claim11326
