import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39684

noncomputable section

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

abbrev Perm7 := MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697.Perm7

/-- Claim 39684: in the concrete affine Borel, the intersection with the
normal Heisenberg seven-core is the normal Sylow-seven subgroup, and the
corresponding quotient-order ratio is prime to seven. -/
def claim39684 : Prop :=
  ∀ Γ : Subgroup Perm7, Γ ≤ affineBorel7 →
    let P := heisenbergCore7 Γ
    normalSylow7 P Γ ∧
      Nat.Coprime (Nat.card Γ / Nat.card P) 7

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39684
