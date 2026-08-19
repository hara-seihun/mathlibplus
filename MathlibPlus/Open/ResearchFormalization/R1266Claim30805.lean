import MathlibPlus.Open.Research.FormalizationBatch.R1266Claim30808

namespace MathlibPlus.Open.ResearchFormalization.R1266

noncomputable section
open Polynomial
open MathlibPlus.Open.Research.R1266

/-- The discriminant of the zero-`x₂` double-star quadratic. -/
def discriminant30805 (a b : ℕ) : RationalFunction :=
  C1 a b ^ 2 - 4 * C0 a b * (J a * J b)

/-- The comparison square used for the boundary residual. -/
def comparisonSquare30805 (a b : ℕ) : RationalFunction :=
  (1 + rationalX) ^ a * rationalX ^ (b - 1) *
    (rationalX ^ 2 + rationalX + (b : RationalFunction))

/-- The low-order leading coefficient of a rational function, read from its
canonical numerator. -/
def lowLeadingCoefficient30805 (R : RationalFunction) : ℚ :=
  (RatFunc.num R).trailingCoeff

def rationalSquare30805 (q : ℚ) : Prop :=
  ∃ z : ℚ, z ^ 2 = q

/-- Claim 30805: every boundary discriminant is nonsquare; the exceptional
boundary is tied to the residual discriminant coefficient `69`, rather than
being asserted as an unrelated standalone nonsquare. -/
def claim30805 : Prop :=
  ∀ (a b : ℕ),
    2 ≤ a →
      2 ≤ b →
        a = 2 * b - 1 →
          lowLeadingCoefficient30805 (discriminant30805 a b) =
              ((b : ℚ) + 4) ^ 2 - 20 ∧
            ((a, b) ≠ (3, 2) →
              ¬ rationalSquare30805 (((b : ℚ) + 4) ^ 2 - 20)) ∧
            ((a, b) = (3, 2) →
              lowLeadingCoefficient30805
                  (discriminant30805 a b - comparisonSquare30805 a b ^ 2) =
                69 ∧
                ¬ rationalSquare30805 69) ∧
            ¬ ∃ q : RationalFunction, q ^ 2 = discriminant30805 a b

end
end MathlibPlus.Open.ResearchFormalization.R1266
