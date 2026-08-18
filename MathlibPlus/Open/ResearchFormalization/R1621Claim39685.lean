import MathlibPlus.Open.ResearchFormalization.R1621Claim39686

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39685

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

/-- Claim 39685: on the exact affine-Borel action carrier, every translation
that preserves all orbits of the normal Heisenberg core also preserves all
orbits of the containing affine-Borel subgroup. -/
def claim39685 : Prop :=
  ∀ Γ : Subgroup Perm7,
    Γ ≤ affineBorel7 →
      translationStabilizer7 (heisenbergCore7 Γ) ⊆
        translationStabilizer7 Γ

end MathlibPlus.Open.ResearchFormalization.R1621Claim39685
