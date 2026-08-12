import Mathlib.Tactic

namespace MathlibPlus.Algebra

/-!
Formalization of admitted claim 18389.  The source writes the coefficient on
`tau₁` and `tau₂` as `p^(-1/2)` but does not specify an ambient operator
algebra.  Here `a` is that coefficient in a commutative scalar algebra, and
`hhalf` records `a^2 = p⁻¹`; no positivity or primality of `p` is needed for
the displayed algebraic expansion.
-/

/-- The rank-two tensorized BX-face expansion. -/
theorem tensorizedBXFaceExpansion_claim18389 {R : Type*} [Field R]
    (p a τ₁ τ₂ : R) (hhalf : a ^ 2 = p⁻¹) :
    (1 - a * τ₁) * (1 - a * τ₂) =
      1 - a * (τ₁ + τ₂) + p⁻¹ * (τ₁ * τ₂) := by
  calc
    (1 - a * τ₁) * (1 - a * τ₂) =
        1 - a * (τ₁ + τ₂) + a ^ 2 * (τ₁ * τ₂) := by ring
    _ = 1 - a * (τ₁ + τ₂) + p⁻¹ * (τ₁ * τ₂) := by rw [hhalf]

end MathlibPlus.Algebra
