import Mathlib

namespace MathlibPlus.Analysis.AdaptiveTreeFourierData

/--
Claim 50873.  The three-bit assignment convention is the packet's one: bit
`0` is the root query, and the two branch queries are bits `2` and `1`.
The conditional-variance definitions make the stated root/branch cost and area
explicit rather than importing an unformalized decision-tree interface.
-/
theorem adaptiveTreeRecordOne
    :
    let r : (Fin 8) → (Fin 3) → ℚ := fun a i =>
      if Nat.testBit a.val i.val then 1 else -1
    let T : (Fin 8) → ℚ := fun a =>
      if Nat.testBit a.val 0 then r a 1 else r a 2
    let walsh : (Fin 8) → ℚ := fun mask =>
      (∑ a : Fin 8,
        (∏ i : Fin 3,
          if Nat.testBit mask.val i.val then r a i else 1) * T a) / 8
    let count : Nat → Nat → ℚ := fun mask bits =>
      ∑ a : Fin 8, if Nat.land a.val mask = bits then 1 else 0
    let mean : Nat → Nat → ℚ := fun mask bits =>
      (∑ a : Fin 8, if Nat.land a.val mask = bits then T a else 0) /
        count mask bits
    let variance : Nat → Nat → ℚ := fun mask bits =>
      (∑ a : Fin 8,
        if Nat.land a.val mask = bits then (T a - mean mask bits) ^ 2 else 0) /
        count mask bits
    let continuationCost : Nat → Nat → ℚ := fun mask bits =>
      if variance mask bits = 0 then 0 else 1
    let treeCost : ℚ :=
      if variance 0 0 = 0 then 0 else
        1 + (continuationCost 1 0 + continuationCost 1 1) / 2
    let treeArea : ℚ := variance 0 0 + (variance 1 0 + variance 1 1) / 2
    T = ![-1, -1, -1, 1, 1, -1, 1, 1] ∧
      treeCost = 2 ∧ treeArea = 2 ∧
      walsh 2 = 1 / 2 ∧
      walsh 4 = 1 / 2 ∧
      walsh 3 = 1 / 2 ∧
      walsh 5 = -(1 / 2) ∧
      ∀ mask : Fin 8, mask ≠ 2 → mask ≠ 3 → mask ≠ 4 → mask ≠ 5 →
        walsh mask = 0 := by
  native_decide

end MathlibPlus.Analysis.AdaptiveTreeFourierData
