import MathlibPlus.Open.Analysis.ThetaHeatClaim19067
import MathlibPlus.Open.Analysis.ThetaDerivativeHBClaim19084

open Filter Topology

namespace MathlibPlus.Open.Analysis.VerticalShiftExact

noncomputable section

abbrev EntireFunction := ℂ → ℂ

def realRootedFunction (F : EntireFunction) : Prop :=
  (∃ z : ℂ, F z ≠ 0) ∧ ∀ z : ℂ, F z = 0 → z.im = 0

def verticalTranslate (F : EntireFunction) (ω : ℝ) : EntireFunction :=
  fun z => F (z + Complex.I * (ω : ℂ))

def verticalLowerTranslate (F : EntireFunction) (ω : ℝ) : EntireFunction :=
  fun z => F (z - Complex.I * (ω : ℂ))

def verticalSharp (F : EntireFunction) (ω : ℝ) : EntireFunction :=
  fun z => starRingEnd ℂ ((verticalTranslate F ω) (starRingEnd ℂ z))

def verticalAverage (F : EntireFunction) (ω : ℝ) : EntireFunction :=
  fun z =>
    ((verticalTranslate F ω) z + (verticalSharp F ω) z) / 2

def locallyUniformVerticalLimit (F : EntireFunction) : Prop :=
  ∀ ω : ℕ → ℝ, Antitone ω → Tendsto ω atTop (𝓝 0) →
    ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, z ∈ K →
        ‖verticalAverage F (ω n) z - F z‖ < ε

/-- Vertical translates, their reflected partners, the real-part average, the
strict Hermite--Biehler implication, and the one-sequence Hurwitz converse. -/
def claim19086 : Prop :=
  ∀ τ : ℝ,
    let F : EntireFunction :=
      MathlibPlus.Open.Analysis.Claim19067.literalHeatTransform τ
    (∀ ω : ℝ, 0 < ω →
      (∀ z : ℂ,
        verticalSharp F ω z = F (z - Complex.I * (ω : ℂ))) ∧
      (∀ z : ℂ,
        verticalAverage F ω z =
          (F (z + Complex.I * (ω : ℂ)) +
            F (z - Complex.I * (ω : ℂ))) / 2)) ∧
    (realRootedFunction F →
      ∀ ω : ℝ, 0 < ω →
        MathlibPlus.Open.Analysis.Claim19084.hermiteBiehler
          (verticalTranslate F ω) (verticalSharp F ω)) ∧
    locallyUniformVerticalLimit F ∧
    ((∃ ω : ℕ → ℝ,
        Antitone ω ∧ (∀ n : ℕ, 0 < ω n) ∧
          Tendsto ω atTop (𝓝 0) ∧
          (∀ n : ℕ, realRootedFunction (verticalAverage F (ω n)))) →
      realRootedFunction F)

end
end MathlibPlus.Open.Analysis.VerticalShiftExact
