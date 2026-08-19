import Mathlib

namespace MathlibPlus.TwoSheetKernel

noncomputable section

/-- Claim 4689's exact two-sheet exponential kernel. -/
def pointKernel (q r : ℝ) : ℝ :=
  r ^ (-(5 : ℝ) / 4) * Real.exp (-q / r) +
    r ^ ((5 : ℝ) / 4) * Real.exp (-q * r)

def arithmeticQ (x : ℝ) : ℝ :=
  Real.pi * x ^ 2

def spectralR (u : ℝ) : ℝ :=
  Real.exp (2 * u)

/-- Claim 4690: reciprocal-sheet exchange leaves the point kernel invariant. -/
def reciprocalSymmetry (q r : ℝ) : Prop :=
  0 < r → pointKernel q r = pointKernel q (1 / r)

/-- Claim 4691: the point kernel has the central hyperbolic form on the
exponential spectral coordinate. -/
def centralForm (q t : ℝ) : Prop :=
  pointKernel q (Real.exp t) =
    2 * Real.exp (-q * Real.cosh t) *
      Real.cosh (5 * t / 4 - q * Real.sinh t)

/-- Claim 4693: the point kernel is strictly positive on the positive-r,
nonnegative-q chamber. -/
def pointKernel_pos (q r : ℝ) : Prop :=
  0 ≤ q → 0 < r → 0 < pointKernel q r

end

end MathlibPlus.TwoSheetKernel
