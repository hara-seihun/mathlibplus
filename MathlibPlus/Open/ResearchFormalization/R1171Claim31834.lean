import MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim31834

noncomputable section

open MathlibPlus.Open.GroupTheory.R1171RawShearClaims31836_31837

/-- Membership in the translation-stabilizer subspace specified for `P_f`. -/
def fiberPeriodCondition (f : FiberFunction) (u : FiberBase) : Prop :=
  ∀ m : fiberDerivativeModule f,
    fiberTranslate u (m : FiberFunction) = (m : FiberFunction)

/-- Claim 31834: the center of the exact generated image has the stated
cardinality, with `P_f` represented by its exact fixed-point submodule. -/
def claim31834 : Prop :=
  ∀ (f : FiberFunction),
    f 0 = 0 →
      ∃ P : Submodule FiberField FiberBase,
        (∀ u : FiberBase, u ∈ P ↔ fiberPeriodCondition f u) ∧
          Nat.card (Subgroup.center (fiberGeneratedImage f)) =
            5 ^ (1 + Module.finrank FiberField P)

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim31834
