import Mathlib

namespace MathlibPlus.Open.Analysis

open MeasureTheory

noncomputable section

/--
Claim 13204.  The pushforward of normalized Haar measure on the complex unit
circle by `z ↦ z + z⁻¹` is the arcsine equilibrium measure on `[-2,2]`.

`Circle` has no default measurable-space instance in this Mathlib snapshot, so
this node installs its Borel measurable structure locally.  The endpoint values
of the density are immaterial to the measure; the displayed `withDensity`
chooses Lean's canonical value there.
-/
def cyclotomicEquilibriumMeasure_13204 : Prop :=
  letI : MeasurableSpace Circle := borel Circle
  letI : BorelSpace Circle := ⟨rfl⟩
  ∃ ν : Measure Circle,
    Measure.IsHaarMeasure ν ∧
      ν Set.univ = 1 ∧
      Measure.map
          (fun z : Circle => ((z : ℂ) + (z : ℂ)⁻¹).re) ν =
        Measure.withDensity volume (fun u : ℝ =>
          if u ∈ Set.Icc (-2 : ℝ) 2 then
            ENNReal.ofReal (1 / (Real.pi * Real.sqrt (4 - u ^ 2)))
          else 0)

end
end MathlibPlus.Open.Analysis
