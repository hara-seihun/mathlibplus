import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Positive integer indices for the Jacobi coefficients. -/
abbrev JacobiIndex := {j : ℕ // 1 ≤ j}

/-- The scale associated with the `j`-th positive Jacobi coefficient. -/
def jacobiScale (a : JacobiIndex → ℝ) (j : JacobiIndex) : ℝ :=
  (2 * a j)⁻¹

/-- The hypotheses on the positive Jacobi coefficients used by the batch. -/
def EventuallyStrictlyDecreasingToZero (a : JacobiIndex → ℝ) : Prop :=
  (∀ j, 0 < a j) ∧
    (∀ᶠ j in Filter.atTop, ∀ k, j < k → a k < a j) ∧
    Filter.Tendsto a Filter.atTop (nhds 0)

/-- The counting function of the positive scales. -/
def jacobiCount (a : JacobiIndex → ℝ) (T : ℝ) : ℕ :=
  Set.ncard {j : JacobiIndex | jacobiScale a j ≤ T}

/-- The local arcsine phase. -/
def arcsinePhase (u : ℝ) : ℝ :=
  if 0 ≤ u ∧ u ≤ 1 then Real.pi⁻¹ * Real.arccos u else 0

/-- The phase sum built from the positive Jacobi scales. -/
def phaseSum (a : JacobiIndex → ℝ) (T : ℝ) : ℝ :=
  ∑' j : JacobiIndex, arcsinePhase (jacobiScale a j / T)

/-- Claim 8847: the exact Abel convolution identity. -/
def claim8847 (a : JacobiIndex → ℝ) : Prop :=
  EventuallyStrictlyDecreasingToZero a →
    ∀ T : ℝ, 0 < T →
      phaseSum a T / T =
        Real.pi⁻¹ *
          ∫ u in (0 : ℝ)..1,
            ((jacobiCount a (T * u) : ℝ) / T) / Real.sqrt (1 - u ^ 2)

/-- The log-scale counting function `H(x) = exp(-x) M(exp x)`. -/
def logScaleCount (a : JacobiIndex → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-x) * (jacobiCount a (Real.exp x) : ℝ)

/-- The one-sided log-scale kernel. -/
def logScaleKernel (v : ℝ) : ℝ :=
  Real.exp (-2 * v) /
    (Real.pi * Real.sqrt (1 - Real.exp (-2 * v)))

/-- Claim 8848: the one-sided log-scale convolution and its two kernel forms. -/
def claim8848 (a : JacobiIndex → ℝ) : Prop :=
  EventuallyStrictlyDecreasingToZero a →
    (∀ x : ℝ,
      phaseSum a (Real.exp x) / Real.exp x =
        ∫ v in Set.Ici (0 : ℝ),
          logScaleKernel v * logScaleCount a (x - v)) ∧
      (∀ v : ℝ, 0 ≤ v →
        logScaleKernel v =
          1 /
            (Real.pi * Real.exp v *
              Real.sqrt (Real.exp (2 * v) - 1)))

end

end MathlibPlus.Open.Analysis
