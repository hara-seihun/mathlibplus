import MathlibPlus.Open.ResearchFormalization.R1201AffineOffsets41941

namespace MathlibPlus.Open.ResearchFormalization.R1201Claim32170

open MathlibPlus.Open.ResearchFormalization.R1201AffineOffsets41941

noncomputable section

/-- Both nonlinear support branches force the proper-fiber offsets to have
one common affine form. -/
def affineOffsetsInNonlinearBranches_claim32170 : Prop :=
  (∀ (fibers : C7 → Set C7) (r : C7 → C7)
      (δ : C7 → Equiv.Perm C7),
    pointCoPointFiberProfile fibers →
      nonlinearFiberCondition δ →
        shiftedDerivativeCompatibility (properFiberSupport fibers) r δ →
          affineOnSupport (properFiberSupport fibers) r) ∧
  (∀ (fibers : C7 → Set C7) (r : C7 → C7)
      (δ : C7 → Equiv.Perm C7) (F : Set (Set C7)),
    fanoLineComplementFiberProfile fibers F →
      nonlinearFiberCondition δ →
        shiftedDerivativeCompatibility (properFiberSupport fibers) r δ →
          affineOnSupport (properFiberSupport fibers) r)

end

end MathlibPlus.Open.ResearchFormalization.R1201Claim32170
