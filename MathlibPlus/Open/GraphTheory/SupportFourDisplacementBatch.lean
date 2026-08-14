import Mathlib

namespace MathlibPlus.Open.GraphTheory.SupportFour

abbrev Fiber := Fin 2 → ZMod 3

/-- The displacement subgroup of a fiber permutation. -/
def displacementSubgroup (q : Fiber ≃ Fiber) : AddSubgroup Fiber :=
  AddSubgroup.closure {w : Fiber |
    ∃ t : Fiber, w = t - q t + q 0}

def isFiberTranslation (q : Fiber ≃ Fiber) : Prop :=
  ∃ c : Fiber, ∀ t, q t = t + c

def isProperNonzeroDisplacement (q : Fiber ≃ Fiber) : Prop :=
  displacementSubgroup q ≠ ⊥ ∧ displacementSubgroup q ≠ ⊤ ∧
    Nat.card (displacementSubgroup q) = 3

/-- Claim 37561. -/
def claim37561_displacementSubgroupOfFiberRow : Prop :=
  ∀ q : Fiber ≃ Fiber,
    (displacementSubgroup q = ⊥ ↔ isFiberTranslation q) ∧
    (displacementSubgroup q ≠ ⊥ →
      displacementSubgroup q = ⊤ ∨ isProperNonzeroDisplacement q) ∧
    (isProperNonzeroDisplacement q →
      displacementSubgroup q ≠ ⊤) ∧
    (displacementSubgroup q = ⊤ →
      Nat.card (displacementSubgroup q) = Fintype.card Fiber)

end MathlibPlus.Open.GraphTheory.SupportFour
