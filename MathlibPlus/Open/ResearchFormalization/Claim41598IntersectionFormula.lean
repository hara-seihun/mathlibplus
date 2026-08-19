import MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837

namespace MathlibPlus.Open.ResearchFormalization.Claim41598

open MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837

noncomputable section

/-- Claim 41598: for the exact normalized fibre-shear carrier, the
constant-difference subspace has the displayed dimension and determines the
intersection of the two regular copies. -/
def claim41598 : Prop :=
  ∀ (f : FiberFunction),
    f 0 = 0 →
      ∃ U : Submodule FiberField FiberBase,
        (∀ u : FiberBase,
          u ∈ U ↔
            ∃ c : FiberField,
              ∀ v : FiberBase, fiberDerivative f u v = c) ∧
          Nat.card (↥(fiberTranslations ⊓ fiberTarget f)) =
            5 ^ (1 + Module.finrank FiberField U)

end

end MathlibPlus.Open.ResearchFormalization.Claim41598
