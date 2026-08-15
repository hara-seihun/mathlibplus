import Mathlib

namespace MathlibPlus.Open.Research.DifferentialRatioCompleteness

/-- The relation-data carrier supplied by the admitted graded up-down relation. -/
def RelationData (K : Type*) [Field K] := Kˣ × (ℕ → K)

/-- The grading-gauge orbit action on relation data. -/
def gradingGaugeOrbit {K : Type*} [Field K]
    (x y : RelationData K) : Prop :=
  ∃ c γ₀ : Kˣ,
    y.1 = c * x.1 ∧
      ∀ n : ℕ, y.2 n = (γ₀ : K) * ((c : K) ^ n) * x.2 n

/-- Positive indices for the differential-ratio sequence. -/
def DifferentialRatioIndex := {n : ℕ // 1 ≤ n}

/-- The sequence λₙ = rₙ/(q rₙ₋₁), on its stated range n ≥ 1. -/
def differentialRatioSequence {K : Type*} [Field K]
    (x : RelationData K) : DifferentialRatioIndex → K :=
  fun n => x.2 n.1 / ((x.1 : K) * x.2 (n.1 - 1))

/--
Completeness of the differential-ratio sequence: for nonvanishing relation
scalars, equality of all differential ratios is equivalent to membership in the
same grading-gauge orbit.
-/
def differentialRatioSequenceComplete (K : Type*) [Field K] : Prop :=
  ∀ x y : RelationData K,
    (∀ n : ℕ, x.2 n ≠ 0) →
    (∀ n : ℕ, y.2 n ≠ 0) →
      (gradingGaugeOrbit x y ↔
        differentialRatioSequence x = differentialRatioSequence y)

end MathlibPlus.Open.Research.DifferentialRatioCompleteness
