import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39686

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

/-- Claim 39686: for every literal affine-Borel subgroup, the common
translation stabilizer of all its W-orbits equals that of its exact
Heisenberg core P=Gamma intersect N. -/
def claim39686 : Prop :=
  ∀ Γ : Subgroup Perm7,
    Γ ≤ affineBorel7 →
      translationStabilizer7 Γ =
        translationStabilizer7 (heisenbergCore7 Γ)

end MathlibPlus.Open.ResearchFormalization.R1621Claim39686
