import MathlibPlus.Open.TreeSpectral

namespace MathlibPlus.Open.ResearchFormalization.TreePrimitiveTowers5956_5957

open MathlibPlus.Open.TreeSpectral

noncomputable section

/-- Claim 5956: the concrete primitive kernel at bottom degree `m` and its
iterated graft image in degree `m + k`. -/
def primitiveBottomSpaceAndGraftTower_claim5956 : Prop :=
  ∀ (m k : ℕ),
    let primitive : Submodule ℚ (TreeSpace m) :=
      LinearMap.ker (leafDeletion m)
    let towerAtDepth : Submodule ℚ (TreeSpace (m + k)) :=
      Submodule.map (graftPow m k) primitive
    (∀ v : TreeSpace m,
      v ∈ primitive ↔ leafDeletion m v = 0) ∧
      (∀ v : TreeSpace m,
        v ∈ primitive → graftPow m k v ∈ towerAtDepth) ∧
      (∀ w : TreeSpace (m + k),
        w ∈ towerAtDepth →
          ∃ v : TreeSpace m, v ∈ primitive ∧ graftPow m k v = w)

/-- Claim 5957: the concrete graft towers span each graded level, and in the
stable range they are the corresponding `GL` eigenspaces with distinct depth
labels. -/
def graftingDepthDecomposition_claim5957 : Prop :=
  (∀ (n : ℕ),
    (⊤ : Submodule ℚ (TreeSpace n)) =
      ⨆ (k : Fin (Nat.succ n)),
        tower n k.val (Nat.le_of_lt_succ k.isLt)) ∧
  (∀ (n k : ℕ) (hn : 0 < n),
    ∀ (hTop : 2 ≤ n) (hDepth : k ≤ n) (hBottom : 2 ≤ n - k),
      tower n k hDepth =
              Module.End.eigenspace (glOperator n hn) (spectralLabel n k) ∧
            ∀ (j : ℕ),
              j ≤ n →
                2 ≤ n - j →
                  k ≠ j → spectralLabel n k ≠ spectralLabel n j)

end

end MathlibPlus.Open.ResearchFormalization.TreePrimitiveTowers5956_5957
