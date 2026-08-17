import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim39687

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

/-- The exact affine-Borel exceptional case for the common translation
stabilizer, with the Heisenberg core and translation core on `F₇²`. -/
def claim39687 : Prop :=
  ∀ Γ : Subgroup Perm7, Γ ≤ affineBorel7 →
    let P := heisenbergCore7 Γ
    let V := translationCore7 Γ
    let exceptional :=
      Nat.card P = 49 ∧ transitive7 P ∧
        translationCore7 P = flagVectors7
    ((¬ exceptional → translationStabilizer7 Γ = V) ∧
      (exceptional →
        translationStabilizer7 Γ = (Set.univ : Set W7)) ∧
      (strictlyContains7 V (translationStabilizer7 Γ) ↔ exceptional))

end MathlibPlus.Open.ResearchFormalization.Batch_7e3f7a79_Claim39687
