import MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

namespace MathlibPlus.Open.ResearchFormalization.Claim39683AffineBorelHeisenberg

noncomputable section

open MathlibPlus.Open.Geometry.HeisenbergBorel39693_39697

private def translationOrbitStabilizerDefinition
    (K : Subgroup Perm7) : Prop :=
  translationStabilizer7 K =
    {t : W7 | ∀ x y : W7,
      y ∈ orbit7 K x ↔ translate7 t y ∈ orbit7 K x}

/-- Claim 39683: the exact F₇² affine Borel contains its normal affine
    Heisenberg Sylow-seven subgroup, and the arbitrary-K translation stabilizer
    is the displayed orbit-preserving translation set. -/
def affineBorelHeisenbergCore_claim39683 : Prop :=
  shearGroup7 ≤ linearBorel7 ∧
    heisenbergGroup7 ≤ affineBorel7 ∧
      normalSylow7 heisenbergGroup7 affineBorel7 ∧
        (∀ K : Subgroup Perm7, translationOrbitStabilizerDefinition K) ∧
          (∀ Γ : Subgroup Perm7, Γ ≤ affineBorel7 →
            heisenbergCore7 Γ = Γ ⊓ heisenbergGroup7 ∧
              translationCore7 Γ =
                {t : W7 | translate7 t ∈ Γ})

end

end MathlibPlus.Open.ResearchFormalization.Claim39683AffineBorelHeisenberg
