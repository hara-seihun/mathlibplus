import MathlibPlus.Open.ResearchFormalization.R2071

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization.R2071Claim36025

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2071

/-- The number of members of the actual augmented family containing a given
coordinate. -/
def coordinateSupportCount (M t s : ℕ)
    (x : BackboneCoordinate M t ⊕ Fin (M ^ t)) : ℕ :=
  ((augmentedFamily M t s).filter (fun A => x ∈ A)).card

/-- The normalized frequency of a coordinate in the actual family. -/
def normalizedCoordinateFrequency (M t s : ℕ)
    (x : BackboneCoordinate M t ⊕ Fin (M ^ t)) : ℝ :=
  (coordinateSupportCount M t s x : ℝ) /
    ((augmentedFamily M t s).card : ℝ)

/-- The normalized pivot mean of an actual augmented member. -/
def normalizedPivotMean (M t s : ℕ)
    (A : Finset (BackboneCoordinate M t ⊕ Fin (M ^ t))) : ℝ :=
  ∑ x ∈ A, normalizedCoordinateFrequency M t s x

/-- The exact two-layer support counts of the complete-graph-dual product and
cyclic augmentation. -/
def coordinateLayerSupportFacts (M t s : ℕ) : Prop :=
  (∀ e : BackboneCoordinate M t,
    coordinateSupportCount M t s (Sum.inl e) = 2 * M ^ (t - 1)) ∧
  (∀ k : Fin (M ^ t),
    coordinateSupportCount M t s (Sum.inr k) = s)

/-- The maximum-frequency assertion is expressed over the actual finite ground
set by its upper-bound and attained-value clauses. -/
def maximumFrequencyEquals (M t s : ℕ) (value : ℝ) : Prop :=
  (∀ x : BackboneCoordinate M t ⊕ Fin (M ^ t),
    normalizedCoordinateFrequency M t s x ≤ value) ∧
  (∃ x : BackboneCoordinate M t ⊕ Fin (M ^ t),
    normalizedCoordinateFrequency M t s x = value)

/-- The exact low-frequency and normalized-pivot identities for the actual
cyclic augmented family. -/
def lowFrequencyPivotIdentities (M t s : ℕ) : Prop :=
  coordinateLayerSupportFacts M t s ∧
    maximumFrequencyEquals M t s
      (max ((2 : ℝ) / (M : ℝ))
        ((s : ℝ) / ((M ^ t : ℕ) : ℝ))) ∧
    (∀ A ∈ augmentedFamily M t s,
      normalizedPivotMean M t s A =
        (2 : ℝ) * ((M - 1 : ℕ) : ℝ) * (t : ℝ) / (M : ℝ) +
          (s : ℝ) ^ 2 / ((M ^ t : ℕ) : ℝ))

/-- Claim 36025: the actual complete-graph-dual product has the displayed
coordinate-frequency maximum and pivot means, together with the stated
small-parameter consequence. -/
def claim36025 : Prop :=
  (∀ (M t s : ℕ),
    admissibleParameters M t s →
      cyclicConstructionFacts M t s →
        lowFrequencyPivotIdentities M t s) ∧
  (∀ ε : ℝ, 0 < ε →
    ∃ M : ℕ, (4 : ℝ) / ε < (M : ℝ) ∧
      ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
        ∀ s : ℕ,
          admissibleParameters M t s →
            cyclicConstructionFacts M t s →
              max ((2 : ℝ) / (M : ℝ))
                  ((s : ℝ) / ((M ^ t : ℕ) : ℝ)) < ε ∧
                (∀ A ∈ augmentedFamily M t s,
                  normalizedPivotMean M t s A < ε))

end
end MathlibPlus.Open.ResearchFormalization.R2071Claim36025
