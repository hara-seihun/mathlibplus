import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

/-- The interval represented by one pair of endpoints in a layer decomposition.
The two domain endpoints are included exactly when they belong to the strict
superlevel set. -/
def layerCakeInterval (w : ℝ → ℝ) (ξ t : ℝ) (p : ℝ × ℝ) : Set ℝ :=
  {u | p.1 ≤ u ∧ u ≤ p.2 ∧
    (p.1 < u ∨ (p.1 = 1 ∧ w p.1 > t)) ∧
    (u < p.2 ∨ (p.2 = ξ ∧ w p.2 > t))}

/-- A finite-perimeter interval component of a strict superlevel set on
`[1, ξ]`, recorded by its two endpoints. -/
def isLayerCakeIntervalComponent
    (w : ℝ → ℝ) (ξ t : ℝ) (p : ℝ × ℝ) : Prop :=
  1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ ξ ∧
    (∀ u ∈ Set.Ioo p.1 p.2, w u > t) ∧
    (p.1 = 1 ∨ w p.1 ≤ t) ∧
    (p.2 = ξ ∨ w p.2 ≤ t)

/-- The packet's finite family of interval components is the decomposition of
`{u ∈ [1, ξ] | w u > t}`. -/
def isLayerCakeComponentDecomposition
    (w : ℝ → ℝ) (ξ t : ℝ) (components : Finset (ℝ × ℝ)) : Prop :=
  (∀ p ∈ components, isLayerCakeIntervalComponent w ξ t p) ∧
    (∀ ⦃p q : ℝ × ℝ⦄, p ∈ components → q ∈ components → p ≠ q →
      p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
    (∀ u : ℝ, u ∈ Set.Icc 1 ξ →
      (w u > t ↔ ∃ p ∈ components, u ∈ layerCakeInterval w ξ t p))

/-- The first moment denoted by `μ_ξ(w)` in the admitted layer-cake claim. -/
noncomputable def layerCakeMu (ξ : ℝ) (w : ℝ → ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..ξ, u * w u

/-- Layer-cake component identities for a nonnegative normalized `C¹` weight.
The component family is the same finite interval-component family in all three
identities. -/
def layerCakeComponentIdentities : Prop :=
  ∀ (ξ : ℝ) (w : ℝ → ℝ) (components : ℝ → Finset (ℝ × ℝ)),
    1 < ξ →
    ContDiffOn ℝ 1 w (Set.Icc 1 ξ) →
    (∀ u ∈ Set.Icc 1 ξ, 0 ≤ w u) →
    (∫ u in (1 : ℝ)..ξ, w u) = 1 →
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      isLayerCakeComponentDecomposition w ξ t (components t)) →
    ((∫ u in (1 : ℝ)..ξ, w u / u) =
        (∫ t, (∑ p ∈ components t, Real.log (p.2 / p.1))
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ∧
      layerCakeMu ξ w =
        (∫ t, (∑ p ∈ components t, (p.2 ^ 2 - p.1 ^ 2) / 2)
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ∧
      1 =
        (∫ t, (∑ p ∈ components t, (p.2 - p.1))
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))))

end MathlibPlus.Open.Analysis
