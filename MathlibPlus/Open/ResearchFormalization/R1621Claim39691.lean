import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39691

noncomputable section

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

/-- Claim 39691: a Heisenberg core with nonzero shear projection and trivial
flag-line intersection is cyclic of order seven and has zero common
translation stabilizer. -/
def claim39691_cyclic_shear_core_classification : Prop :=
  ∀ (Γ : Subgroup Perm7), Γ ≤ affineBorel7 →
    let P := heisenbergCore7 Γ
    ¬ P ≤ translationGroup7 →
      P ⊓ flagTranslationGroup7 = (⊥ : Subgroup Perm7) →
        (∃ g : Perm7, P = generatedBy7 g) ∧
          Nat.card P = 7 ∧
            translationStabilizer7 P = ({(0 : W7)} : Set W7)

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39691
