import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The first moment denoted by `μ_ξ(w)` in the admitted claim. -/
noncomputable def layerCakeFirstMoment (ξ : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..ξ, u * w u

/--
A finite family of interval components of the superlevel set of a weight on
`[1, ξ]`.  The characterization is relative to the interior of the domain;
this leaves the endpoint traces to the endpoint values `1` and `ξ`, as in the
coarea statement accompanying the admitted claim.
-/
def IsLayerCakeIntervalComponentFamily
    (ξ : ℝ) (w : ℝ → ℝ)
    (components : ℝ → Finset (ℝ × ℝ)) : Prop :=
  ∀ᵐ t ∂MeasureTheory.volume, 0 < t →
    (∀ p ∈ components t, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ ξ) ∧
    (∀ p ∈ components t, ∀ q ∈ components t, p ≠ q →
      p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
    (∀ u ∈ Set.Ioo (1 : ℝ) ξ,
      (w u > t ↔ ∃ p ∈ components t, u ∈ Set.Ioo p.1 p.2)) ∧
    (∀ p ∈ components t, ∀ a b : ℝ,
      1 ≤ a → b ≤ ξ → a < b → a ≤ p.1 → p.2 ≤ b →
      (∀ u ∈ Set.Ioo a b, w u > t) →
      a = p.1 ∧ b = p.2)

/-- The three layer-cake component identities in the admitted statement. -/
def layerCakeComponentIdentities : Prop :=
  ∀ (ξ : ℝ) (w : ℝ → ℝ)
    (components : ℝ → Finset (ℝ × ℝ)),
    1 ≤ ξ →
    (∀ u ∈ Set.Icc (1 : ℝ) ξ, 0 ≤ w u) →
    ContDiffOn ℝ 1 w (Set.Icc (1 : ℝ) ξ) →
    (∫ u in (1 : ℝ)..ξ, w u) = 1 →
    IsLayerCakeIntervalComponentFamily ξ w components →
    (∫ u in (1 : ℝ)..ξ, w u / u) =
      (∫ t, (components t).sum (fun p => Real.log (p.2 / p.1))
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    layerCakeFirstMoment ξ w =
      (∫ t, (components t).sum (fun p => (p.2 ^ 2 - p.1 ^ 2) / 2)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    (1 : ℝ) =
      (∫ t, (components t).sum (fun p => p.2 - p.1)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))

end MathlibPlus.Open.Analysis
