import MathlibPlus.Open.ResearchFormalizationBatch_01a001b3_443b_7727_a88a_7b55e0d6fe72.Linear

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a001b3_443b_7727_a88a_7b55e0d6fe72

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Claim 5154.  With the atomic core fixed, the column and row sides of a
frozen radius ball are the recursively accumulated incidence neighborhoods:
columns take one shared-block step at a time, while rows are the incident
blocks of the preceding column balls. -/
def claim5154_frozenRadiusBalls : Prop :=
  ∀ (F R V B : Type) [Field F] [Fintype R] [Fintype V] [Fintype B]
    [DecidableEq B] [DecidableEq V]
    (M : Matrix R V F) (block : R → B) (S₀ : Finset V),
    atomicCoreProperty M block S₀ →
      ∀ (v : V), v ∈ S₀ →
        radiusColumns M block S₀ v 0 = {v} ∧
          radiusBlocks M block S₀ v 0 = ∅ ∧
          (∀ r : ℕ,
            radiusColumns M block S₀ v (r + 1) =
                radiusColumns M block S₀ v r ∪
                  (radiusColumns M block S₀ v r).biUnion
                    (fun w => columnNeighbors M block S₀ w) ∧
              radiusBlocks M block S₀ v (r + 1) =
                radiusBlocks M block S₀ v r ∪
                  (radiusColumns M block S₀ v r).biUnion
                    (fun w => incidentBlocks M block w)) ∧
          (∀ r : ℕ, radiusColumns M block S₀ v r ⊆ S₀)

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a001b3_443b_7727_a88a_7b55e0d6fe72
