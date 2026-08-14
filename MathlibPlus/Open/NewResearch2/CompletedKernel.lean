import Mathlib

namespace MathlibPlus.Open.NewResearch2.CompletedKernel

noncomputable section
open Set

/-- The centered completed-function value obtained after the exact boundary term. -/
def centeredCompletedValue (T : ℝ → ℝ) (h : ℝ) : ℝ :=
  1 / 2 + 2 * (h ^ 2 - 1 / 4) *
    ∫ u in Ioi (0 : ℝ), T u * Real.exp (u / 2) * Real.cosh (h * u)

def claim4647_exact_integration_by_parts_completion
    (X T : ℝ → ℝ) : Prop :=
  ∀ h : ℝ,
    X h = 1 / 2 + 2 * (h ^ 2 - 1 / 4) *
      ∫ u in Ioi (0 : ℝ), T u * Real.exp (u / 2) * Real.cosh (h * u)

def squareVariableKernelTransform (T : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), T u * Real.exp (u / 2) * Real.cosh (u * Real.sqrt w)

def claim4648_square_variable_kernel_transform
    (A : ℝ → ℝ) (T : ℝ → ℝ) : Prop :=
  (∀ w : ℝ, 0 ≤ w →
    A w = ∫ u in Ioi (0 : ℝ), T u * Real.exp (u / 2) *
      Real.cosh (u * Real.sqrt w)) ∧
  (∀ (w y₁ y₂ : ℝ), 0 ≤ w → y₁ ^ 2 = w → y₂ ^ 2 = w →
    (∫ u in Ioi (0 : ℝ), T u * Real.exp (u / 2) * Real.cosh (u * y₁)) =
      ∫ u in Ioi (0 : ℝ), T u * Real.exp (u / 2) * Real.cosh (u * y₂))

def affineBoundaryFamily (T : ℝ → ℝ) (c w : ℝ) : ℝ :=
  c + 2 * (w - 1 / 4) * squareVariableKernelTransform T w

def claim4649_affine_boundary_family (H : ℝ → ℝ) (T : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ w : ℝ,
    H w = c + 2 * (w - 1 / 4) * squareVariableKernelTransform T w

def descendedLogarithmicDerivative (T : ℝ → ℝ) (c z : ℝ) : ℝ :=
  deriv (affineBoundaryFamily T c) (-z) /
    affineBoundaryFamily T c (-z)

def claim4652_descended_logarithmic_derivative
    (F : ℝ → ℝ) (T : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ z : ℝ,
    affineBoundaryFamily T c (-z) ≠ 0 →
    F z = deriv (affineBoundaryFamily T c) (-z) /
      affineBoundaryFamily T c (-z)

end
end MathlibPlus.Open.NewResearch2.CompletedKernel
