import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The normalized Gamma density on the positive radial half-line. -/
noncomputable def gammaDensity (a u : ℝ) : ℝ :=
  Real.rpow u (a - 1) * Real.exp (-u) / Real.Gamma a

noncomputable def gammaMeasure (a : ℝ) : MeasureTheory.Measure ℝ :=
  (MeasureTheory.Measure.restrict
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ)
      (Set.Ioi (0 : ℝ))).withDensity
    (fun u => ENNReal.ofReal (gammaDensity a u))

/-- The inner product formula in the Gamma radial space. -/
noncomputable def gammaInner (a : ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ u, star (f u) * g u ∂(gammaMeasure a)

/-- The centered Rankin differential expression from the repair context. -/
noncomputable def centeredRankinGenerator (a : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) * deriv f u + ((a - u) / 2 : ℂ) * f u

/-- The closed translation `exp (z A_a)`, written through the logarithmic model. -/
noncomputable def rankinExponential (a z : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u =>
    (Real.exp (a * z / 2 - (Real.exp z - 1) * u / 2) : ℂ) *
      f (Real.exp z * u)

/-- The logarithmic unitary formula fixing the canonical realization. -/
noncomputable def logarithmicUnitary (a : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (a * x / 2 - Real.exp x / 2) : ℂ) * f (Real.exp x) /
    (Real.sqrt (Real.Gamma a) : ℂ)

noncomputable def phaseSign (ε : Fin 2) : ℝ := if ε = 0 then 1 else -1

/-- The two phase vectors `u^(± i τ/2)` in the common real-shape Gamma space. -/
noncomputable def phaseVector (τ : ℝ) (ε : Fin 2) : ℝ → ℂ :=
  fun u => Complex.cpow (u : ℂ) (Complex.I * (phaseSign ε * τ / 2))

noncomputable def phaseCoefficientKernel (a τ : ℝ) : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
  fun z ε η => gammaInner a (phaseVector τ ε) (rankinExponential a z (phaseVector τ η))

noncomputable def sech (z : ℝ) : ℝ := 1 / Real.cosh (z / 2)

noncomputable def gammaPlus (a τ : ℝ) : ℂ :=
  Complex.Gamma ((a : ℂ) + Complex.I * τ) / Complex.Gamma (a : ℂ)

noncomputable def gammaMinus (a τ : ℝ) : ℂ :=
  Complex.Gamma ((a : ℂ) - Complex.I * τ) / Complex.Gamma (a : ℂ)

noncomputable def phaseKernelMatrix (a τ z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun ε η =>
    if ε = 0 ∧ η = 0 then
      Complex.exp (Complex.I * (τ : ℂ) * (z : ℂ) / 2) *
        Complex.cpow (sech z : ℂ) (a : ℂ)
    else if ε = 0 ∧ η = 1 then
      gammaMinus a τ * Complex.cpow (sech z : ℂ) ((a : ℂ) - Complex.I * τ)
    else if ε = 1 ∧ η = 0 then
      gammaPlus a τ * Complex.cpow (sech z : ℂ) ((a : ℂ) + Complex.I * τ)
    else
      Complex.exp (-Complex.I * (τ : ℂ) * (z : ℂ) / 2) *
        Complex.cpow (sech z : ℂ) (a : ℂ)

noncomputable def complexMatrixPosSemidef
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  M.IsHermitian ∧
    ∀ v : Fin 2 → ℂ,
      0 ≤ (∑ i, ∑ j, star (v i) * M i j * v j).re

/-- Positive definiteness of a two-by-two matrix-valued translation kernel. -/
noncomputable def matrixValuedPositiveDefinite
    (K : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → Fin 2 → ℂ),
    0 ≤ (∑ i, ∑ j, ∑ ε, ∑ η,
      star (c i ε) * K (x i - x j) ε η * c j η).re

/-- Claim 7809: the closed phase-paired translation kernel and its strict zero-frequency bound. -/
noncomputable def closedPhasePairedTranslationKernel : Prop :=
  ∀ (a τ : ℝ), 0 < a →
    matrixValuedPositiveDefinite (phaseCoefficientKernel a τ) ∧
    (∀ z : ℝ, phaseCoefficientKernel a τ z = phaseKernelMatrix a τ z) ∧
    complexMatrixPosSemidef (phaseCoefficientKernel a τ 0) ∧
    ‖gammaPlus a τ‖ ≤ 1 ∧
    (τ ≠ 0 → ‖gammaPlus a τ‖ < 1)

end MathlibPlus.Open.Analysis
