import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

def normalizedChebyshevPsiError (x : ℝ) : ℝ :=
  |Chebyshev.psi x - x| / x

def logarithmicScale (x : ℝ) : ℝ :=
  Real.log x

def squareRootLogEnvelope (A d x : ℝ) : ℝ :=
  A * Real.rpow (Real.log x) (3 / 2 : ℝ) *
    Real.exp (-d * Real.sqrt (Real.log x))

def normalizedChebyshevPsiErrorAndSquareRootEnvelope : Prop :=
  ∀ (x : ℝ), 1 < x →
    normalizedChebyshevPsiError x = |Chebyshev.psi x - x| / x ∧
    logarithmicScale x = Real.log x ∧
    ∀ (A d : ℝ),
      squareRootLogEnvelope A d x =
        A * Real.rpow (Real.log x) (3 / 2 : ℝ) *
          Real.exp (-d * Real.sqrt (Real.log x))

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
