import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R0098

/-- Claim 17922: the Laguerre parameter for a Euclidean dimension is `d / 2 - 1`. -/
def laguerre_parameter_radial_dimension (d : ℕ) (α : ℝ) : Prop :=
  α = (d : ℝ) / 2 - 1

/-- Claim 17925: dimensions one and three give the two half-integer parameters. -/
def half_integer_radial_channels : Prop :=
  (-(1 : ℝ) / 2 = (1 : ℝ) / 2 - 1) ∧
    ((1 : ℝ) / 2 = (3 : ℝ) / 2 - 1)

end MathlibPlus.Open.FormalizationBatch.R0098
