import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The golden-ratio frequency lower bound for finite nontrivial
    union-closed families. -/
def goldenRatioFrequency_claim19955 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (𝓕 : Finset (Finset α)),
    𝓕.Nonempty →
    𝓕 ≠ {∅} →
    (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ∪ B ∈ 𝓕) →
    ∃ x : α,
      ((𝓕.filter (fun A => x ∈ A)).card : ℝ) ≥
        ((3 - Real.sqrt 5) / 2) * (𝓕.card : ℝ)

end MathlibPlus.Open.Combinatorics
