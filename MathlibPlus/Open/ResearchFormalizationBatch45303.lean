import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

section InverseCell

noncomputable def cellProbability
    {R X T : Type*} [Fintype X]
    (pX : R → X → ℝ) (H : R → X → T) (r : R) (t : T) : ℝ := by
  classical
  exact ∑ x, if H r x = t then pX r x else 0

noncomputable def cellMean
    {R X T : Type*} [Fintype X]
    (pX : R → X → ℝ) (H : R → X → T) (μ : X → ℝ)
    (r : R) (t : T) : ℝ := by
  classical
  let q := cellProbability pX H r t
  exact if 0 < q then
    (∑ x, if H r x = t then pX r x * μ x else 0) / q
  else 0

noncomputable def cellVariance
    {R X T : Type*} [Fintype X]
    (pX : R → X → ℝ) (H : R → X → T) (μ : X → ℝ)
    (r : R) (t : T) : ℝ := by
  classical
  let q := cellProbability pX H r t
  let m := cellMean pX H μ r t
  exact if 0 < q then
    (∑ x, if H r x = t then pX r x * (μ x - m) ^ 2 else 0) / q
  else 0

noncomputable def inverseCellFactor
    {T : Type*} (q : T → ℝ) (t : T) : ℝ :=
  if 0 < q t then (q t)⁻¹ else 0

noncomputable def expectedPosteriorVariance
    {R X T : Type*} [Fintype R] [Fintype X] [Fintype T]
    (pR : R → ℝ) (pX : R → X → ℝ) (H : R → X → T)
    (μ : X → ℝ) : ℝ := by
  classical
  exact ∑ r, pR r * ∑ t,
    cellProbability pX H r t * cellVariance pX H μ r t

noncomputable def inverseCellPairExpectation
    {R X T : Type*} [Fintype R] [Fintype X]
    (pR : R → ℝ) (pX : R → X → ℝ) (H : R → X → T)
    (μ : X → ℝ) : ℝ := by
  classical
  exact ∑ r, pR r * ∑ x, pX r x * ∑ x', pX r x' *
    ((μ x - μ x') ^ 2 *
      (if H r x = H r x' then
        inverseCellFactor (cellProbability pX H r) (H r x)
      else 0))

noncomputable def unweightedSameTranscriptPairExpectation
    {R X T : Type*} [Fintype R] [Fintype X]
    (pR : R → ℝ) (pX : R → X → ℝ) (H : R → X → T)
    (μ : X → ℝ) : ℝ := by
  classical
  exact ∑ r, pR r * ∑ x, pX r x * ∑ x', pX r x' *
    ((μ x - μ x') ^ 2 * if H r x = H r x' then 1 else 0)

def finiteConditionalProbabilityData
    {R X : Type*} [Fintype R] [Fintype X]
    (pR : R → ℝ) (pX : R → X → ℝ) : Prop :=
  (∀ r, 0 ≤ pR r) ∧
  (∑ r, pR r = 1) ∧
  (∀ r x, 0 ≤ pX r x) ∧
  (∀ r, ∑ x, pX r x = 1)

def inverseCellPosteriorVarianceIdentity : Prop :=
  ∀ {R X T : Type*} [Fintype R] [Fintype X] [Fintype T]
    (pR : R → ℝ) (pX : R → X → ℝ) (H : R → X → T) (μ : X → ℝ),
    finiteConditionalProbabilityData pR pX →
      expectedPosteriorVariance pR pX H μ =
        (1 / 2 : ℝ) * inverseCellPairExpectation pR pX H μ

/-- The unweighted same-transcript replacement is not an equivalent formula. -/
def inverseCellFactorIsNecessary : Prop :=
  ¬ ∀ (pR : Unit → ℝ) (pX : Unit → Fin 3 → ℝ)
      (H : Unit → Fin 3 → Fin 2) (μ : Fin 3 → ℝ),
    finiteConditionalProbabilityData pR pX →
      expectedPosteriorVariance pR pX H μ =
        (1 / 2 : ℝ) *
          unweightedSameTranscriptPairExpectation pR pX H μ

end InverseCell

end MathlibPlus.Open.ResearchFormalizationBatch
