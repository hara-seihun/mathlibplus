import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable def gammaEvenAppellPositiveIntegerShape : Prop :=
  ∀ (q : ℕ) (θ : ℝ), 1 ≤ q → 0 < θ →
    let gammaLaw : MeasureTheory.Measure ℝ :=
      MeasureTheory.Measure.withDensity MeasureTheory.MeasureSpace.volume
        (ProbabilityTheory.gammaPDF (q : ℝ) (1 / θ))
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (Z : Ω → ℝ),
      ProbabilityTheory.IdentDistrib Z (fun x : ℝ => x) μ gammaLaw →
      ∀ (r : ℕ) (hr : 1 ≤ r),
        (∀ (y : Fin r → ℝ),
          0 < y ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hr⟩ ∧ StrictMono y →
            0 < Matrix.det
              (fun (i j : Fin r) =>
                ∫ ω, (y i + Z ω) ^ (2 * (j : ℕ)) ∂μ)) ∧
        (∀ (n : Fin r → ℕ) (y : Fin r → ℝ),
          (∀ i, 0 < n i) → StrictMono n →
          (∀ i,
            Real.log (n i : ℝ) < y i ∧
              y i < Real.log ((n i + 1 : ℕ) : ℝ)) →
            0 < Matrix.det
              (fun (i j : Fin r) =>
                ∫ ω, (y i + Z ω) ^ (2 * (j : ℕ)) ∂μ))

end MathlibPlus.Open.Probability
