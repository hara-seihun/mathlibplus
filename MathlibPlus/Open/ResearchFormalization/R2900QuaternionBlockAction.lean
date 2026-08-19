import MathlibPlus.Open.ResearchFormalization.R2900QuaternionClaims

namespace MathlibPlus.Open.ResearchFormalization.R2900BlockActionRepair

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2900

/-- The R-2900 setup with only the source hypotheses: the two induced
order-four regular block-action conclusions are intentionally not included. -/
def quaternionBlockHypotheses_claim47398
    {J V B : Type*} [Fintype V] [Fintype B]
    (relations : J → V → V → Prop)
    (A : Subgroup (Equiv.Perm V))
    (blocks : B → Set V) (n : ℕ)
    (R T : Subgroup (Equiv.Perm V))
    (hR : R ≤ A) (hT : T ≤ A)
    (eR : QuaternionGroup n ≃* R) (eT : QuaternionGroup n ≃* T)
    (CR CT : Subgroup (QuaternionGroup n))
    (zR : R) (zT : T)
    (blockAction : A →* Equiv.Perm B) : Prop :=
  (∀ f : Equiv.Perm V,
    f ∈ A ↔ relationalAutomorphism relations f) ∧
  fourOddBlockPartition blocks n ∧
  (∀ a : A, ∀ b : B,
    blocks (blockAction a b) = (a : Equiv.Perm V) '' blocks b) ∧
  R ≤ A ∧ T ≤ A ∧
  regularPermutationCopy R eR ∧
  regularPermutationCopy T eT ∧
  characteristicCyclicQuaternionSubgroup n CR ∧
  characteristicCyclicQuaternionSubgroup n CT ∧
  hasIndexedOrbitPartition
    (R.subtype.comp eR.toMonoidHom) CR blocks ∧
  hasIndexedOrbitPartition
    (T.subtype.comp eT.toMonoidHom) CT blocks ∧
  uniqueNontrivialInvolution zR ∧
  uniqueNontrivialInvolution zT

/-- Claim 47398, repaired: the exact quaternion/block hypotheses imply the
actual regular cyclic order-four actions induced on the four blocks. -/
def quaternionBlockAction_claim47398 : Prop :=
  ∀ (J V B : Type*) [Fintype V] [Fintype B]
    (relations : J → V → V → Prop)
    (A : Subgroup (Equiv.Perm V))
    (blocks : B → Set V) (n : ℕ)
    (R T : Subgroup (Equiv.Perm V))
    (hR : R ≤ A) (hT : T ≤ A)
    (eR : QuaternionGroup n ≃* R) (eT : QuaternionGroup n ≃* T)
    (CR CT : Subgroup (QuaternionGroup n))
    (zR : R) (zT : T)
    (blockAction : A →* Equiv.Perm B),
    quaternionBlockHypotheses_claim47398 relations A blocks n R T hR hT
      eR eT CR CT zR zT blockAction →
      regularCyclicFourBlockAction
        (blockAction.comp (Subgroup.inclusion hR)) zR ∧
      regularCyclicFourBlockAction
        (blockAction.comp (Subgroup.inclusion hT)) zT

end

end MathlibPlus.Open.ResearchFormalization.R2900BlockActionRepair
