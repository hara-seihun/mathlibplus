import Mathlib
import MathlibPlus.Open.ResearchFormalization.K0124

namespace MathlibPlus.Open.ResearchFormalization.K0124

open MeasureTheory
open scoped BigOperators Topology

noncomputable def reciprocalCapMeasure8876 : Measure ℝ :=
  Measure.restrict
    (Measure.withDensity volume (fun z : ℝ => ENNReal.ofReal ((z⁻¹) ^ 2)))
    (Set.Ioi 0)

noncomputable def empiricalMeasure8876
    (z : ℕ → ℕ → ℝ) (n : ℕ) (S : Finset ℕ) : Measure ℝ :=
  ((n : ENNReal)⁻¹) • (Finset.sum S (fun i => Measure.dirac (z n i)))

def empiricalWeakLimit8876 (z : ℕ → ℕ → ℝ) (μ : Measure ℝ) : Prop :=
  ∃ S : ℕ → Finset ℕ,
    (∀ n, (S n).card = n ∧ ∀ i ∈ S n, 1 ≤ i) ∧
      ∀ f : ℝ → ℝ,
        Continuous f →
          (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |f x| ≤ C) →
            Filter.Tendsto
              (fun n => ∫ x, f x ∂(empiricalMeasure8876 z n (S n)))
              Filter.atTop
              (𝓝 (∫ x, f x ∂μ))

def reciprocalCapClass8876 (μ : Measure ℝ) : Prop :=
  0 ≤ μ ∧
    μ Set.univ = 1 ∧
      μ (Set.Iic 0) = 0 ∧
        μ ≤ reciprocalCapMeasure8876

noncomputable def logarithmicEnergy8876
    (μ : { μ : Measure ℝ // reciprocalCapClass8876 μ }) : ℝ :=
  ∫ z, (∫ w, Real.log |z ^ 2 - w ^ 2| ∂(μ : Measure ℝ)) ∂(μ : Measure ℝ)

def claim8876 (z : ℕ → ℕ → ℝ) : Prop :=
  claim8872 z →
    ∀ μ : Measure ℝ,
      empiricalWeakLimit8876 z μ →
        reciprocalCapClass8876 μ

end MathlibPlus.Open.ResearchFormalization.K0124
