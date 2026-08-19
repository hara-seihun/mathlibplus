import Mathlib.GroupTheory.SpecificGroups.Quaternion

namespace MathlibPlus.GroupTheory.Claim14586

/-- Claim 14586: the canonical generalized quaternion group at parameter two
has the eight displayed elements and the defining Q8 relations. -/
def quaternionGroupTwo_q8_relations_claim14586 : Prop :=
  let i : QuaternionGroup 2 := QuaternionGroup.a 1
  let j : QuaternionGroup 2 := QuaternionGroup.xa 0
  let k : QuaternionGroup 2 := i * j
  let negOne : QuaternionGroup 2 := QuaternionGroup.a 2
  Fintype.card (QuaternionGroup 2) = 8 ∧
    (∀ x : QuaternionGroup 2,
      x = QuaternionGroup.a 0 ∨ x = QuaternionGroup.a 1 ∨
        x = QuaternionGroup.a 2 ∨ x = QuaternionGroup.a 3 ∨
        x = QuaternionGroup.xa 0 ∨ x = QuaternionGroup.xa 1 ∨
        x = QuaternionGroup.xa 2 ∨ x = QuaternionGroup.xa 3) ∧
    i ^ 2 = negOne ∧ j ^ 2 = negOne ∧ k ^ 2 = negOne ∧
      i * j * k = negOne

end MathlibPlus.GroupTheory.Claim14586
