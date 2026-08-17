import Mathlib
import MathlibPlus.Algebra.FamilyProduct

namespace MathlibPlus.Open.NewResearch2.R0316Repair

noncomputable section

private def traceCoupled
    {X Y : Type*} [Fintype X] [Fintype Y]
    (support : Set (Set Y)) (fiber : Set Y → Set (Set X)) : Prop :=
  (∀ S T : Set Y, S ∈ support → T ∈ support → S ∪ T ∈ support) ∧
    (∀ S : Set Y, S ∈ support → (fiber S).Nonempty) ∧
    (∀ S T : Set Y, S ∈ support → T ∈ support →
      MathlibPlus.Algebra.FamilyProduct.familyProduct (fiber S) (fiber T) ⊆
        fiber (S ∪ T))

private def innerLift {X Y : Type*} (A : Set X) : Set (Sum X Y) :=
  Sum.inl '' A

private def outerLift {X Y : Type*} (S : Set Y) : Set (Sum X Y) :=
  Sum.inr '' S

private def reconstructedFamily
    {X Y : Type*} (support : Set (Set Y)) (fiber : Set Y → Set (Set X)) :
    Set (Set (Sum X Y)) :=
  {U | ∃ S : Set Y, S ∈ support ∧ ∃ A : Set X, A ∈ fiber S ∧
    U = innerLift A ∪ outerLift S}

/-- Claim 19739: on disjoint finite grounds, the support is union-closed and
its nonempty inner fibers form a lax join map for the exact family product. -/
def claim19739_traceCoupledFiberSystem
    {X Y : Type*} [Fintype X] [Fintype Y]
    (support : Set (Set Y)) (fiber : Set Y → Set (Set X)) : Prop :=
  traceCoupled support fiber

/-- Claim 19740: the displayed disjoint-sum reconstruction is an ordinary
family, and disjoint trace labels make each reconstructed member's pair of
support and inner-fiber labels unique. -/
def claim19740_reconstructionFromCoupledFibers
    {X Y : Type*} [Fintype X] [Fintype Y]
    (support : Set (Set Y)) (fiber : Set Y → Set (Set X)) : Prop :=
  traceCoupled support fiber ∧
    (∀ U : Set (Sum X Y),
      U ∈ reconstructedFamily support fiber ↔
        ∃ S : Set Y, S ∈ support ∧ ∃ A : Set X, A ∈ fiber S ∧
          U = innerLift A ∪ outerLift S) ∧
    (∀ S T : Set Y, S ∈ support → T ∈ support →
      ∀ A B : Set X, A ∈ fiber S → B ∈ fiber T →
        innerLift A ∪ outerLift S = innerLift B ∪ outerLift T →
          S = T ∧ A = B)

end

end MathlibPlus.Open.NewResearch2.R0316Repair
