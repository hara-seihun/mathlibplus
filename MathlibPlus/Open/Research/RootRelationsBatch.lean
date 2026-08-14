import Mathlib

namespace MathlibPlus.Open.Research

/-- A concrete predicate for a complex root of unity. -/
def IsRootOfUnity (z : ℂ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ z ^ n = 1

/-- Claim 20327: the coefficient alternatives forced by a weighted relation
among three roots of unity. -/
def weightedThreeRootRelationClassification : Prop :=
  ∀ (A0 A1 A2 : ℤ) (v0 v1 v2 : ℂ),
    (IsRootOfUnity v0 ∧ IsRootOfUnity v1 ∧ IsRootOfUnity v2 ∧
      (A0 : ℂ) * v0 + (A1 : ℂ) * v1 + (A2 : ℂ) * v2 = 0) →
    ∃ δ1 δ2 : ℤ,
      ((δ1 = 1 ∨ δ1 = -1) ∧ (δ2 = 1 ∨ δ2 = -1)) ∧
        ((A0 + δ1 * A1 + δ2 * A2 = 0) ∨
          (A1 = δ1 * A0 ∧ A2 = δ2 * A0))

/-- The Eisenstein coefficient `A + B*ω`, with integer coefficients. -/
def eisensteinTerm (A B : ℤ) (ω : ℂ) : ℂ :=
  (A : ℂ) + (B : ℂ) * ω

/-- Membership in the rational span of `1` and `ω`. -/
def rationalEisensteinSpan (ω z : ℂ) : Prop :=
  ∃ q r : ℚ, z = (q : ℂ) + (r : ℂ) * ω

/-- Claim 20328: nonzero Eisenstein triangle contributions have a ratio in
`ℚ(ω)` which is a sixth root of unity; the zero case is retained as well. -/
def eisensteinTriangleContributionRatio : Prop :=
  ∀ (A B C D : ℤ) (v w ω : ℂ),
    (IsRootOfUnity v ∧ IsRootOfUnity w ∧ ω ^ 2 + ω + 1 = 0 ∧
      v * eisensteinTerm A B ω + w * eisensteinTerm C D ω = 0) →
    ((eisensteinTerm A B ω = 0 ∧ eisensteinTerm C D ω = 0) ∨
      (eisensteinTerm A B ω ≠ 0 ∧ eisensteinTerm C D ω ≠ 0 ∧
        rationalEisensteinSpan ω
          (-(eisensteinTerm A B ω) / eisensteinTerm C D ω) ∧
        (-(eisensteinTerm A B ω) / eisensteinTerm C D ω) = w / v ∧
        (-(eisensteinTerm A B ω) / eisensteinTerm C D ω) ^ 6 = 1))

end MathlibPlus.Open.Research
