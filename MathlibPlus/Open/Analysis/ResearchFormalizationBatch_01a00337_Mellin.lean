import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The real compactly supported zero-mean `L¹` source class from claim 3727. -/
def CompactZeroMeanL1MellinDensity (a R : ℝ) (q : ℝ → ℝ) : Prop :=
  0 < a ∧ a < R ∧
    MeasureTheory.Integrable q ∧
    Function.support q ⊆ Set.Icc a R ∧
    (¬ ∀ᵐ x ∂MeasureTheory.volume, q x = 0) ∧
    (∫ x in a..R, q x) = 0

/-- The Mellin transform used by claims 3727--3731. -/
def mellinTransform (a R : ℝ) (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x in a..R, (q x : ℂ) * Complex.cpow (x : ℂ) (s - 1)

/-- The factor called `A(s)` in claim 3727. -/
def completedMellinFactor (s : ℂ) : ℂ :=
  ((1 : ℂ) / 2) * s * (s - 1) * Complex.cpow (Real.pi : ℂ) (-s / 2) * Complex.Gamma (s / 2)

/-- The completed symmetrization from claim 3727. -/
def completedMellinSymmetrization (a R : ℝ) (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  ((1 : ℂ) / 2) *
    (mellinTransform a R q s / completedMellinFactor s +
      mellinTransform a R q (1 - s) / completedMellinFactor (1 - s))

/-- The full compact zero-mean source datum and its displayed transforms. -/
def compactZeroMeanL1MellinSource (a R : ℝ) (q : ℝ → ℝ) : Prop :=
  CompactZeroMeanL1MellinDensity a R q ∧
    (∀ s : ℂ,
      mellinTransform a R q s =
        ∫ x in a..R, (q x : ℂ) * Complex.cpow (x : ℂ) (s - 1)) ∧
    (∀ s : ℂ,
      completedMellinSymmetrization a R q s =
        ((1 : ℂ) / 2) *
          (mellinTransform a R q s / completedMellinFactor s +
            mellinTransform a R q (1 - s) / completedMellinFactor (1 - s)))

/-- A standard explicit meaning of entire of exponential type. -/
def EntireOfExponentialType (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧
    ∃ C τ : ℝ, 0 ≤ C ∧ 0 ≤ τ ∧
      ∀ s : ℂ, ‖F s‖ ≤ C * Real.exp (τ * ‖s‖)

/-- Entire continuation and dominated differentiation for the Mellin transform. -/
def entireMellinContinuationAndDerivativeFormula
    (a R : ℝ) (q : ℝ → ℝ) : Prop :=
  CompactZeroMeanL1MellinDensity a R q →
    EntireOfExponentialType (mellinTransform a R q) ∧
      ∀ (k : ℕ) (s : ℂ),
        iteratedDeriv k (mellinTransform a R q) s =
          ∫ x in a..R,
            (q x : ℂ) * Complex.cpow (x : ℂ) (s - 1) *
              ((Real.log x : ℂ) ^ k)

/-- The endpoint transform `G_q` and the factorization in claim 3731. -/
def endpointTransform (a R : ℝ) (q : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..Real.log (R / a),
    (q (a * Real.exp u) : ℂ) * Complex.exp (-w * (u : ℂ))

def endpointMellinFactorization (a R : ℝ) (q : ℝ → ℝ) : Prop :=
  CompactZeroMeanL1MellinDensity a R q →
    let D : ℝ := Real.log (R / a)
    MeasureTheory.IntegrableOn (fun u : ℝ => q (a * Real.exp u)) (Set.Icc 0 D) ∧
      (∀ s : ℂ,
        mellinTransform a R q (1 - s) =
          Complex.cpow (a : ℂ) (1 - s) * endpointTransform a R q (s - 1)) ∧
      (∃ w : ℂ, endpointTransform a R q w ≠ 0) ∧
      AnalyticOnNhd ℂ (endpointTransform a R q) {w : ℂ | 0 < w.re} ∧
      (∃ C : ℝ, 0 ≤ C ∧
        ∀ w : ℂ, 0 < w.re → ‖endpointTransform a R q w‖ ≤ C)

end MathlibPlus.Open.Analysis
