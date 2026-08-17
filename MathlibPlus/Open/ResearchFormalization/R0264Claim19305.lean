import MathlibPlus.Open.NewResearch2.R0264Repair

namespace MathlibPlus.Open.ResearchFormalization.R0264Claim19305

noncomputable section

open MathlibPlus.Open.NewResearch2.R0264Repair

/-- The two affine coefficients in the modular integration-by-parts boundary
port. -/
def boundaryPortA (α lam u : ℝ) : ℝ :=
  -(α / 4) * shellBoundaryFactor lam u

def boundaryPortB (lam u : ℝ) : ℝ :=
  shellBoundaryFactor lam u / 4 - 1 / 2

def boundaryPort (α lam u z c : ℝ) : ℝ :=
  (boundaryPortA α lam u + z * boundaryPortB lam u) * c

def transformedKernelZerothCoefficient (α lam u : ℝ) : ℝ :=
  zerothDiagonalCoefficient α lam u

/-- The zeroth transformed-kernel coefficient is the stated expression, with
its modular boundary-port normalization retained. -/
def claim19305 : Prop :=
  (∀ (α lam u z c : ℝ),
    boundaryPort α lam u z c =
      (-(α / 4) * shellBoundaryFactor lam u +
        z * (shellBoundaryFactor lam u / 4 - 1 / 2)) * c) ∧
    (∀ (α lam u : ℝ),
      transformedKernelZerothCoefficient α lam u =
        1 / 2 + shellBoundaryFactor lam u *
          (α * u ^ 2 / 8 - 1 / 4))

end

end MathlibPlus.Open.ResearchFormalization.R0264Claim19305
