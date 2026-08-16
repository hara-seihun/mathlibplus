import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- A positive interval has interior, is order-connected, and lies in `(0, ∞)`. -/
def positiveInterval (I : Set ℝ) : Prop :=
  IsOpen I ∧ I.Nonempty ∧ Set.OrdConnected I ∧ ∀ a ∈ I, 0 < a

/-- The source-generic determinant channel from the admitted radial-kernel claim. -/
def sourceKernelQ (G : ℝ → ℝ) (a : ℝ) : ℝ :=
  a ^ 2 * (deriv G a) ^ 2 - a * G a * deriv G a -
    a ^ 2 * G a * deriv (deriv G) a

/-- Clean source-generic determinants force power kernels. -/
def cleanSourceGenericPowerKernel : Prop :=
  ∀ (I : Set ℝ) (G : ℝ → ℝ),
    positiveInterval I →
    ContDiffOn ℝ 2 G I →
    (∀ a ∈ I, 0 < G a) →
    ((∀ a ∈ I, sourceKernelQ G a = 0) ↔
      ∃ C α : ℝ, 0 < C ∧ ∀ a ∈ I, G a = C * Real.rpow a α)

/-- The exact radial feature/tangent cross-Gram matrix used by the determinant claim. -/
def radialFeatureTangentMatrix (G : ℝ → ℝ) (D A J : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![ G A, D * A * deriv G A;
      -(D * A * deriv G A),
      deriv G A * J - D ^ 2 * (A * deriv G A + A ^ 2 * deriv (deriv G) A) ]

/-- Determinant of a positive power radial kernel. -/
def powerRadialKernelDeterminant : Prop :=
  ∀ (I : Set ℝ) (G : ℝ → ℝ) (C α : ℝ) (A J : ℝ → ℝ) (D : ℝ),
    positiveInterval I →
    ContDiffOn ℝ 2 G I →
    (∀ a ∈ I, 0 < G a) →
    (∀ a ∈ I, G a = C * Real.rpow a α) →
    0 < C →
    A D ∈ I →
    Matrix.det
        (radialFeatureTangentMatrix G D (A D) (J D)) =
      C ^ 2 * α * Real.rpow (A D) (2 * α - 1) * J D

end

end MathlibPlus.Open.Analysis
