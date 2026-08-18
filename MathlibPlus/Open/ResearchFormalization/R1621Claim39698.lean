import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39698

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

noncomputable section

/-- Claim 39698 on the concrete `F₇²` affine-Borel carrier. -/
def claim39698_exactAmbientGroupOrders : Prop :=
  Nat.card affineBorel7 = 12348 ∧
    Nat.card heisenbergGroup7 = 343 ∧
      Nat.card linearBorel7 = 252

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39698
