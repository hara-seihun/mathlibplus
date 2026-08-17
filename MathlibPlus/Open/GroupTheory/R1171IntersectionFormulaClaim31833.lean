import MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837

namespace MathlibPlus.Open.GroupTheory.R1171IntersectionFormulaClaim31833

open R1171RawShearClaims31836_31837

noncomputable section

/-- The regular-copy intersection has the dimension of the constant-difference
subspace, with the central fibre line contributing the leading factor of 5. -/
def exactRegularCopyIntersectionFormula_claim31833 : Prop :=
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

end MathlibPlus.Open.GroupTheory.R1171IntersectionFormulaClaim31833
