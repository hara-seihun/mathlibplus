import Mathlib
import MathlibPlus.Open.Analysis.GreenKernel
import MathlibPlus.NumberTheory.CompletedZetaRadial

open MeasureTheory

namespace MathlibPlus.Open.Analysis.ZeroPotentialDerivativeClaim12928

noncomputable section

/-- The entire Riemann xi carrier on a vertical line. -/
noncomputable def xiLine (σ t : ℝ) : ℂ :=
  MathlibPlus.NumberTheory.CompletedZetaRadial.riemannXi
    ((σ : ℂ) - (t : ℂ) * Complex.I)

/-- Horizontal Laguerre curvature for a complex-valued real-height function. -/
def horizontalLaguerreCurvature (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (deriv f t) - (deriv (deriv f) t * star (f t)).re

/-- The normalized horizontal curvature of the entire xi carrier. -/
def qXi (σ t : ℝ) : ℝ :=
  horizontalLaguerreCurvature (fun u : ℝ => xiLine σ u) t /
    Complex.normSq (xiLine σ t)

/-- The zero-height xi potential in the coordinate `a = σ - 1/2`. -/
def xiZeroHeightPotential (a : ℝ) : ℝ :=
  qXi (1 / 2 + a) 0

/-- The positive theta-kernel moments on the zero-height segment. -/
noncomputable def xiKernelA0 (a : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ),
    MathlibPlus.Analysis.GreenKernel.thetaPhiBase u * Real.cosh (a * u)

noncomputable def xiKernelA1 (a : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ),
    u * MathlibPlus.Analysis.GreenKernel.thetaPhiBase u * Real.sinh (a * u)

noncomputable def xiKernelA2 (a : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ),
    u ^ 2 * MathlibPlus.Analysis.GreenKernel.thetaPhiBase u * Real.cosh (a * u)

noncomputable def xiKernelA3 (a : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ),
    u ^ 3 * MathlibPlus.Analysis.GreenKernel.thetaPhiBase u * Real.sinh (a * u)

/-- The first two normalized moments of the tilted positive xi kernel. -/
def xiKernelM (a : ℝ) : ℝ :=
  xiKernelA1 a / xiKernelA0 a

def xiKernelN (a : ℝ) : ℝ :=
  xiKernelA2 a / xiKernelA0 a

/-- The moment derivatives supplied by the positive-kernel identities. -/
def xiKernelMPrimeValue (a : ℝ) : ℝ :=
  xiKernelN a - xiKernelM a ^ 2

def xiKernelNPrimeValue (a : ℝ) : ℝ :=
  (xiKernelA3 a * xiKernelA0 a -
      xiKernelA2 a * xiKernelA1 a) /
    xiKernelA0 a ^ 2

/-- Claim 12928: the entire-xi zero-height potential has the stated moment
identity and nonnegative, strictly positive away from the center, derivative. -/
def claim12928 : Prop :=
  (∀ u : ℝ, 0 ≤ u →
    0 < MathlibPlus.Analysis.GreenKernel.thetaPhiBase u) ∧
    ∀ a : ℝ, 0 ≤ a → a ≤ 1 / 2 →
      0 < xiKernelA0 a ∧
      xiLine (1 / 2 + a) 0 = ((2 * xiKernelA0 a : ℝ) : ℂ) ∧
      xiZeroHeightPotential a = xiKernelM a ^ 2 + xiKernelN a ∧
      HasDerivAt xiKernelM (xiKernelMPrimeValue a) a ∧
      HasDerivAt xiKernelN (xiKernelNPrimeValue a) a ∧
      HasDerivAt xiZeroHeightPotential
        (2 * xiKernelM a * xiKernelMPrimeValue a +
          xiKernelNPrimeValue a) a ∧
      0 ≤ xiKernelMPrimeValue a ∧
      0 ≤ xiKernelNPrimeValue a ∧
      0 ≤ 2 * xiKernelM a * xiKernelMPrimeValue a +
        xiKernelNPrimeValue a ∧
      (0 < a →
        0 < 2 * xiKernelM a * xiKernelMPrimeValue a +
          xiKernelNPrimeValue a)

end

end MathlibPlus.Open.Analysis.ZeroPotentialDerivativeClaim12928
