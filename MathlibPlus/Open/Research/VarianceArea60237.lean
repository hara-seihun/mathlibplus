-- UNVERIFIED (missing-import): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Open.Research.ProbabilitySupport

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace MathlibPlus.Open.Probability

universe u v w

def claim60237 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type v} [Countable I]
    {A : I → Type w} [∀ i, Fintype (A i)] [∀ i, MeasurableSpace (A i)]
    (X : (i : I) → Ω → A i),
    independentUniformFinite P X →
    ∀ (k m : ℕ) (a b : ℝ) (p : Fin m → ℝ) (S : Fin m → Finset I)
      (Z : Fin m → Ω → ℝ),
      a ≤ b ∧
      (∀ r, 0 ≤ p r) ∧
      (∑ r : Fin m, p r = 1) ∧
      (∀ r, (S r).card ≤ k) ∧
      (∀ r, Measurable (Z r)) ∧
      (∀ r ω, a ≤ Z r ω ∧ Z r ω ≤ b) ∧
      (∀ r, dependsOnCoordinates X (S r) (Z r)) →
      let U := unionCoordinates S
      ∃ e : Fin U.card ≃ U,
        @Measurable Ω ℝ
          (orderedTranscriptSpace U e X U.card (le_rfl)) inferInstance
          (fun ω => ∑ r : Fin m, p r * Z r ω) ∧
        orderedVarianceArea P (fun ω => ∑ r : Fin m, p r * Z r ω) U e X ≤
          (k : ℝ) * (b - a) ^ 2 / 4

def oneComponentUniformSignBound60237
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {I : Type v} [Countable I]
    (X : (i : I) → Ω → Bool) (k : ℕ) (a b c : ℝ) : Prop :=
  independentUniformFinite P X →
    ∀ (S : Fin 1 → Finset I) (Z : Fin 1 → Ω → ℝ),
      a ≤ b ∧
      (S 0).card ≤ k ∧
      Measurable (Z 0) ∧
      (∀ ω, a ≤ Z 0 ω ∧ Z 0 ω ≤ b) ∧
      dependsOnCoordinates X (S 0) (Z 0) →
      let U := unionCoordinates S
      ∃ e : Fin U.card ≃ U,
        @Measurable Ω ℝ
          (orderedTranscriptSpace U e X U.card (le_rfl)) inferInstance
          (Z 0) ∧
        orderedVarianceArea P (Z 0) U e X ≤ c

def sharp60237 : Prop :=
  ∀ (k : ℕ) (a b : ℝ), a ≤ b →
    ∀ c : ℝ, c < (k : ℝ) * (b - a) ^ 2 / 4 →
      ¬ (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] {I : Type v} [Countable I]
        (X : (i : I) → Ω → Bool),
        oneComponentUniformSignBound60237 P X k a b c)

end MathlibPlus.Open.Probability
