import Mathlib

open scoped BigOperators

open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.Batch01.Bernstein

noncomputable section

/-- The first differing transcript coordinate. -/
noncomputable def transcriptFirstDifference
    {d : ℕ} {C : Type*} [Fintype C]
    {A : Fin d → Type*} [∀ i, Fintype (A i)]
    (code : C → ∀ i, A i) (hinj : Function.Injective code)
    (x y : C) : ℕ := by
  classical
  by_cases hxy : x = y
  · exact 0
  · have hex' : ∃ i : Fin d, code x i ≠ code y i := by
      by_contra h
      apply hxy
      apply hinj
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    have hex : (Finset.univ.filter
        (fun i : Fin d => code x i ≠ code y i)).Nonempty := by
      rcases hex' with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
    exact ((Finset.univ.filter
      (fun i : Fin d => code x i ≠ code y i)).min' hex).val

noncomputable def transcriptRho {d : ℕ} {C : Type*} [Fintype C]
    {A : Fin d → Type*} [∀ i, Fintype (A i)]
    (code : C → ∀ i, A i) (hinj : Function.Injective code)
    (x y : C) : ℝ := by
  classical
  exact if x = y then 0 else
    (2 : ℝ)⁻¹ ^ transcriptFirstDifference code hinj x y

def transcriptUltrametric {C : Type*} (rho : C → C → ℝ) : Prop :=
  (∀ x, rho x x = 0) ∧
    (∀ x y, rho x y = rho y x) ∧
    (∀ x y, x ≠ y → 0 < rho x y) ∧
    (∀ x y z, rho x z ≤ max (rho x y) (rho y z))

def finiteProcessMaximum {C Ω : Type*} [Fintype C] [Nonempty C]
    (X : C → Ω → ℝ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset C).sup' Finset.univ_nonempty (fun x => X x ω)

/-- Finite transcript-prefix Bernstein chaining, with the displayed mgf
hypothesis and expected-supremum conclusion. -/
def finiteTranscriptPrefixBernsteinClaim : Prop :=
  ∀ (d b : ℕ), 1 ≤ d → 1 ≤ b →
    ∀ (A : Fin d → Type*) [∀ i, Fintype (A i)],
      (∀ i, Fintype.card (A i) ≤ b) →
      ∀ (C : Type*) [Fintype C] [Nonempty C]
        (code : C → ∀ i, A i),
        (hinj : Function.Injective code) →
        ∀ (Ω : Type*) [MeasurableSpace Ω]
          (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : C → Ω → ℝ),
          (∀ x, Integrable (X x) μ ∧ ∫ ω, X x ω ∂μ = 0) →
          ∀ (σ R : ℝ), 0 < σ → 0 ≤ R →
            (∀ x y (z : ℝ),
              0 ≤ z →
              1 - (z * R * transcriptRho code hinj x y) / 3 > 0 →
              ∫ ω, Real.exp (z * (X x ω - X y ω)) ∂μ ≤
                Real.exp (z ^ 2 * σ ^ 2 * transcriptRho code hinj x y ^ 2 /
                  (2 * (1 - (z * R * transcriptRho code hinj x y) / 3)))) →
            transcriptUltrametric (transcriptRho code hinj) ∧
            ∫ ω, finiteProcessMaximum X ω ∂μ ≤
              4 * σ * Real.sqrt (2 * Real.log (b : ℝ)) +
                (4 * R / 3) * Real.log (b : ℝ)

end

end MathlibPlus.Open.ResearchFormalization.Batch01.Bernstein
