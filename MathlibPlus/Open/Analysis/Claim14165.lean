import MathlibPlus.Basic

namespace MathlibPlus.Open.Analysis

open _root_.MeasureTheory

/--
Claim 14165 for finite nonzero measures supported on the nonnegative half-line.
The Cauchy transform is defined on the right half-plane, where its Bochner
integral is bounded; the real-axis estimate is recorded through real and
imaginary parts so that the source's real inequality is not silently changed
into an order on `ℂ`.
-/
def positiveShiftedLogDerivativeMixtures_claim14165 : Prop :=
  ∀ μ : Measure ℝ, IsFiniteMeasure μ → μ ≠ 0 →
    (∀ r ∈ μ.support, 0 ≤ r) →
    let fμ : ℝ → ℝ := fun u => ∫ r, Real.exp (-r * u) ∂μ
    let Fμ : {z : ℂ // 0 < z.re} → ℂ :=
      fun z => ∫ r, ((z : ℂ) + (r : ℂ))⁻¹ ∂μ
    let Mμ : ℝ := (μ Set.univ).toReal
    fμ 0 = Mμ ∧
      (∀ z : {z : ℂ // 0 < z.re}, 0 < (Fμ z).re) ∧
      (∀ δ : ℝ, ∀ hδ : 0 < δ,
        (Fμ ⟨(δ : ℂ), by exact_mod_cast hδ⟩).im = 0 ∧
        (Fμ ⟨(δ : ℂ), by exact_mod_cast hδ⟩).re ≤ Mμ / δ)

end MathlibPlus.Open.Analysis
