import MathlibPlus.Open.Analysis.NumberTheoryFormalization

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.Analysis.NumberTheory

/-- The real Möbius coefficient used in the reciprocal-zeta Dirichlet block. -/
def reciprocalZetaMobius (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- The untruncated Riesz block appearing in the Mellin transform. -/
def reciprocalZetaQ (z : ℝ) : ℝ :=
  ∑' m : ℕ+, ∑' n : ℕ+,
    reciprocalZetaMobius (m : ℕ) * reciprocalZetaMobius (n : ℕ) *
      Real.rpow ((m : ℝ) * (n : ℝ)) (1 + 2 * z) /
        Real.rpow ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) (3 / 2 + z)

/-- The energy whose Mellin transform is evaluated in the reciprocal-zeta claim. -/
def reciprocalZetaEnergy (X : ℝ) : ℝ :=
  (1 / 2) * ∑' m : ℕ+, ∑' n : ℕ+,
    reciprocalZetaMobius (m : ℕ) * reciprocalZetaMobius (n : ℕ) *
      ((m : ℝ) * (n : ℝ)) /
        Real.rpow ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) (3 / 2) *
      incompleteGammaWindowProfile
        (X * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) /
          ((m : ℝ) ^ 2 * (n : ℝ) ^ 2))

/-- The gamma-weighted reciprocal-zeta integral on the real spectral line. -/
def reciprocalZetaGammaWeightedIntegral (z : ℝ) : ℝ :=
  ∫ t : ℝ,
    (‖Complex.Gamma
        ((((3 : ℂ) / 2) + (z : ℂ) + (t : ℂ) * Complex.I) / 2)‖ ^ 2) /
      (‖riemannZeta
        (((1 : ℂ) / 2) - (z : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)

/-- Claim 9354: reciprocal-zeta Mellin norm and the resulting energy transform. -/
def reciprocalZetaMellinNormClaim : Prop :=
  ∀ z : ℝ,
    -(3 : ℝ) / 2 < z →
    z < -(1 : ℝ) / 2 →
    reciprocalZetaQ z =
        (4 * Real.pi * Real.Gamma (3 / 2 + z))⁻¹ *
          reciprocalZetaGammaWeightedIntegral z ∧
      (∫ X in Ioi (0 : ℝ),
          reciprocalZetaEnergy X * Real.rpow X (z - 1)) =
        ((1 - Real.exp (-2 * z)) / (8 * Real.pi * z)) *
          reciprocalZetaGammaWeightedIntegral z

end MathlibPlus.Open.Analysis.NumberTheory
