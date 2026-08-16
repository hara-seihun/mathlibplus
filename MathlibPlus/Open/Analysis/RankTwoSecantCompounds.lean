import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The rank-two secant polynomial and the rank-two second-compound formula are
expanded in the two non-definitional identities below.  The first leased claim
is omitted because its packet does not provide the carrier of the factor
`S_c` from the atomic-theta factorization. -/
def vandermondeNormalizedSecondSecantCompound_claim14039 : Prop :=
  ∀ (a b x₁ x₂ y₁ y₂ : ℝ),
    x₁ < x₂ →
    y₁ < y₂ →
    let S : ℝ → ℝ → ℝ :=
      fun x y =>
        a ^ 2 + (a * b / 6) * (x + y) +
          (b ^ 2 / 360) * (x ^ 2 + 16 * x * y + y ^ 2)
    (-b ^ 2 / 129600) *
        (-2160 * a ^ 2 +
          60 * a * b * (x₁ + x₂ + y₁ + y₂) +
          b ^ 2 *
            (16 * x₁ * x₂ + x₁ * y₁ + x₁ * y₂ +
              x₂ * y₁ + x₂ * y₂ + 16 * y₁ * y₂)) =
      (S x₁ y₁ * S x₂ y₂ - S x₁ y₂ * S x₂ y₁) /
        ((x₂ - x₁) * (y₂ - y₁))

/-- Under a common dilation of positive ordered squared-age nodes, the exact
rank-two second-compound expression changes sign as stated. -/
def structuralDilationSignChange_claim14042 : Prop :=
  ∀ (a b x₁ x₂ y₁ y₂ : ℝ),
    0 < x₁ → x₁ < x₂ →
    0 < y₁ → y₁ < y₂ →
    b ≠ 0 →
    (∃ R : ℝ,
      0 < R ∧
      ∀ r : ℝ, R ≤ r →
        (-b ^ 2 / 129600) *
            (-2160 * a ^ 2 +
              60 * a * b * (r * x₁ + r * x₂ + r * y₁ + r * y₂) +
              b ^ 2 *
                (16 * (r * x₁) * (r * x₂) +
                  (r * x₁) * (r * y₁) +
                  (r * x₁) * (r * y₂) +
                  (r * x₂) * (r * y₁) +
                  (r * x₂) * (r * y₂) +
                  16 * (r * y₁) * (r * y₂))) < 0) ∧
    (a ≠ 0 →
      ∃ ε : ℝ,
        0 < ε ∧
        ∀ r : ℝ, 0 < r → r ≤ ε →
          (-b ^ 2 / 129600) *
              (-2160 * a ^ 2 +
                60 * a * b * (r * x₁ + r * x₂ + r * y₁ + r * y₂) +
                b ^ 2 *
                  (16 * (r * x₁) * (r * x₂) +
                    (r * x₁) * (r * y₁) +
                    (r * x₁) * (r * y₂) +
                    (r * x₂) * (r * y₁) +
                    (r * x₂) * (r * y₂) +
                    16 * (r * y₁) * (r * y₂))) > 0)

end MathlibPlus.Open.Analysis
