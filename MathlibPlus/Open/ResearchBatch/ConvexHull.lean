import Mathlib

namespace MathlibPlus.Open.ResearchBatch.ConvexHull

open scoped BigOperators

/-- The finite harmonic linear form on a coordinate block. -/
def linearOutput {I : Type*} [Fintype I]
    (c : I → ℂ) (z : I → ℂ) : ℂ :=
  ∑ i, c i * z i

/--
The coordinate-separable product hull has support radius at least the `l1`
coefficient charge, with equality on the unit polydisk.
-/
def claim59063_productHullSupportLowerBound : Prop :=
  ∀ {I : Type*} [Fintype I]
    (c : I → ℂ) (C : I → Set ℂ),
    (∀ i, Convex ℝ (C i) ∧
      Metric.closedBall (0 : ℂ) 1 ⊆ C i) →
    (∀ R : ℝ,
      (∀ z : I → ℂ, (∀ i, z i ∈ C i) →
        ‖linearOutput c z‖ ≤ R) →
      ∑ i, ‖c i‖ ≤ R) ∧
    (∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      ‖linearOutput c z‖ ≤ ∑ i, ‖c i‖) ∧
    ∃ z : I → ℂ,
      (∀ i, z i ∈ Metric.closedBall (0 : ℂ) 1) ∧
      ‖linearOutput c z‖ = ∑ i, ‖c i‖ ∧
      (∀ i, c i = 0 → z i = 0) ∧
      (∀ i, c i ≠ 0 → z i = starRingEnd ℂ (c i) / ‖c i‖)

end MathlibPlus.Open.ResearchBatch.ConvexHull
