import MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias15424

open MeasureTheory Set Classical
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0326PoissonShift15426

noncomputable section

/-- The outside-tail set in the literal/full Poisson split. -/
def outsideTail (L : ℝ) : Set ℝ :=
  {t : ℝ | L < ‖t‖}

/-- The signed (complex-valued) density of the literal-minus-full outside tail.
It is the fixed density of the canonical `poissonDefect`, not an arbitrary
measure or transform callback. -/
noncomputable def outsideTailDensity (q : ℝ → ℝ) (L t : ℝ) : ℂ :=
  if t ∈ outsideTail L then
    -MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias.evenPoissonKernel q t
  else 0

/-- The outside-tail complex measure for the canonical Poisson defect. -/
noncomputable def outsideTailMeasure (q : ℝ → ℝ) (L : ℝ) : ComplexMeasure ℝ :=
  Measure.withDensityᵥ (Measure.restrict volume (outsideTail L))
    (outsideTailDensity q L)

/-- Fourier--Laplace integration against the actual complex-measure carrier. -/
noncomputable def complexMeasureTransform
    (μ : ComplexMeasure ℝ) (z : ℂ) : ℂ :=
  μ.integral
    (fun t : ℝ => Complex.exp (Complex.I * z * (t : ℂ)))
    (ContinuousLinearMap.mul ℝ ℂ)

/-- The translated outside-tail measure `τ = t + L`. -/
noncomputable def shiftedOutsideTailMeasure
    (q : ℝ → ℝ) (L : ℝ) : ComplexMeasure ℝ :=
  (outsideTailMeasure q L).map (fun t : ℝ => t + L)

/-- The real rescaled source hypotheses used by the Poisson carrier. -/
def canonicalPoissonSource (L : ℝ) (q : ℝ → ℝ) : Prop :=
  let lambda := Real.exp L
  Function.Even q ∧
    (∫ t : ℝ, q t) = 0 ∧
      Function.support q ⊆ Set.Icc (-lambda) lambda ∧
        q (-lambda) = 0 ∧
          q lambda = 0

/-- Claim 15426: the outside-tail measure is pushed forward by `t ↦ t+L`,
its translated carrier is supported in the two exact half-lines, and its
transform is the shifted canonical Poisson defect. -/
def claim15426_exactShiftedSupportRepresentation : Prop :=
  ∀ (L : ℝ) (q : ℝ → ℝ),
    canonicalPoissonSource L q →
      let ν := outsideTailMeasure q L
      let μ := ν.map (fun t : ℝ => t + L)
      μ.variation.support ⊆ Set.Iic (0 : ℝ) ∪ Set.Ici (2 * L) ∧
        ∀ z : ℂ,
          Complex.exp (Complex.I * (L : ℂ) * z) *
              MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias.poissonDefect q L z =
            complexMeasureTransform μ z

end

end MathlibPlus.Open.ResearchFormalization.O0326PoissonShift15426
