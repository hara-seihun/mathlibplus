import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0227AdversarialZeros

noncomputable section

/-- The adversarial entire-function family named in Claims 19008 and 19012. -/
noncomputable def adversarialFamily (a c : ℝ) (z : ℂ) : ℂ :=
  (c : ℂ) + Complex.cosh ((a : ℂ) * z)

def oddIntegerMultiple (k : ℤ) : ℂ :=
  ((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I

def positiveArcoshZero (a c : ℝ) (k : ℤ) : ℂ :=
  (((Real.arcosh c : ℝ) : ℂ) + oddIntegerMultiple k) / (a : ℂ)

def negativeArcoshZero (a c : ℝ) (k : ℤ) : ℂ :=
  (-((Real.arcosh c : ℝ) : ℂ) + oddIntegerMultiple k) / (a : ℂ)

/-- Claim 19012: under the stated real parameter conditions, the displayed
positive- and negative-arcosh lattice is exactly the zero set, and every zero
has nonzero real part. -/
def adversarialZeroSet_claim19012 : Prop :=
  ∀ (a c : ℝ), 0 < a → 1 < c →
    {z : ℂ | adversarialFamily a c z = 0} =
        {z : ℂ |
          (∃ k : ℤ, z = positiveArcoshZero a c k) ∨
            ∃ k : ℤ, z = negativeArcoshZero a c k} ∧
      ∀ z : ℂ, adversarialFamily a c z = 0 → z.re ≠ 0

/-- Claim 19013: the parameter choice `a = π/y`, `c = cosh (π*x/y)` plants
all four points of the prescribed symmetric off-axis orbit. -/
def plantedOffAxisOrbit_claim19013 : Prop :=
  ∀ (x y : ℝ), 0 < x → 0 < y →
    let a : ℝ := Real.pi / y
    let c : ℝ := Real.cosh (Real.pi * x / y)
    1 < c ∧
      adversarialFamily a c ((x : ℂ) + (y : ℂ) * Complex.I) = 0 ∧
      adversarialFamily a c ((x : ℂ) - (y : ℂ) * Complex.I) = 0 ∧
      adversarialFamily a c ((-x : ℂ) + (y : ℂ) * Complex.I) = 0 ∧
      adversarialFamily a c ((-x : ℂ) - (y : ℂ) * Complex.I) = 0

end

end MathlibPlus.Open.ResearchFormalization.R0227AdversarialZeros
