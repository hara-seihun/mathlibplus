import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.R1621Claim39692

noncomputable section

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

/-- Claim 39692: in the cyclic nonzero-shear case, a generator has the
specified affine normal form with nonzero shear coefficient. -/
def claim39692_cyclic_shear_generator_normal_form : Prop :=
  ∀ (Γ : Subgroup Perm7), Γ ≤ affineBorel7 →
    let P := heisenbergCore7 Γ
    ¬ P ≤ translationGroup7 →
      P ⊓ flagTranslationGroup7 = (⊥ : Subgroup Perm7) →
        ∃ g : Perm7, ∃ c a b : F7,
          g ∈ P ∧
            P = generatedBy7 g ∧
              c ≠ 0 ∧ cyclicGeneratorFormula7 c a b g

end

end MathlibPlus.Open.ResearchFormalization.R1621Claim39692
