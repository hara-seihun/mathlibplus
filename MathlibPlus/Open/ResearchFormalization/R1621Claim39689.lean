import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39689

noncomputable section

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

/-- Claim 39689: when the Heisenberg core is transitive on `W`, both of the
common translation stabilizers are all of `W`. -/
def claim39689_transitive_core_case : Prop :=
  ∀ (Γ : Subgroup Perm7), Γ ≤ affineBorel7 →
    let P := heisenbergCore7 Γ
    transitive7 P →
      translationStabilizer7 P = (Set.univ : Set W7) ∧
        translationStabilizer7 Γ = (Set.univ : Set W7)

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39689
