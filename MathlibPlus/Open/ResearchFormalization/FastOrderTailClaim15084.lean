import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchO0263

namespace MathlibPlus.Open.ResearchFormalization.FastOrderTailClaim15084

open Filter

noncomputable section

/-- The scale prescribed by `α_L = L / S_L^(2 k_L)`. -/
def scheduledPolyharmonicAlpha
    (S : ℝ → ℝ) (k : ℝ → ℕ) (L : ℝ) : ℝ :=
  L / (S L) ^ (2 * k L)

/-- The schedule hypotheses used for the growing-order tail. -/
def fastOrderSchedule (S : ℝ → ℝ) (k : ℝ → ℕ) : Prop :=
  Tendsto S atTop atTop ∧
    Tendsto
      (fun L : ℝ => S L * Real.log (S L) / L)
      atTop (nhds 0) ∧
    (∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ k L)

/-- The exponentially weighted absolute tail of the scheduled polyharmonic kernel. -/
noncomputable def polyharmonicAbsoluteTail
    (S : ℝ → ℝ) (k : ℝ → ℕ) (u η L : ℝ) : ℝ :=
  ∫ t in Set.Ioi (u * L),
    Real.exp (-η * t) *
      ‖MathlibPlus.Open.Research.O0263.polyharmonicKernel
        (scheduledPolyharmonicAlpha S k L) (k L) t‖

/-- Meaning of an `exp (-(a + o(1)) L)` lower envelope. -/
def lowerExponentialEnvelope (T : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℝ → ℝ,
    Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ L : ℝ in atTop,
        T L ≥ Real.exp (-(a + ε L) * L)

/-- Claim 15084: in the fast-order regime, the absolute tail loses no
exponential rate beyond the external weight; setting the weight to zero gives
an `e^(-o(L))` lower envelope for the unweighted tail. -/
def fastOrderTailLowerEnvelope15084 : Prop :=
  ∀ (S : ℝ → ℝ) (k : ℝ → ℕ) (u η : ℝ),
    fastOrderSchedule S k →
      0 < u →
      0 ≤ η →
      Tendsto (fun L : ℝ => (k L : ℝ) / S L) atTop atTop →
      lowerExponentialEnvelope
        (polyharmonicAbsoluteTail S k u η) (η * u) ∧
        lowerExponentialEnvelope
          (polyharmonicAbsoluteTail S k u 0) 0

end

end MathlibPlus.Open.ResearchFormalization.FastOrderTailClaim15084
