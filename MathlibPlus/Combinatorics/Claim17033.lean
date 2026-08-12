import Mathlib

namespace MathlibPlus.Combinatorics.Claim17033

/-- A binary decision tree has at most `2^height` leaves. -/
theorem numLeaves_le_pow_height {α : Type} (t : BinaryTree α) :
    t.numLeaves ≤ 2 ^ t.height := by
  induction t with
  | nil => simp
  | node v l r ihl ihr =>
    simp only [BinaryTree.numLeaves, BinaryTree.height]
    let h := max l.height r.height
    have hlh : l.height ≤ h := Nat.le_max_left _ _
    have hrh : r.height ≤ h := Nat.le_max_right _ _
    have hl : l.numLeaves ≤ 2 ^ h := by
      exact ihl.trans (Nat.pow_le_pow_right (by decide) hlh)
    have hr : r.numLeaves ≤ 2 ^ h := by
      exact ihr.trans (Nat.pow_le_pow_right (by decide) hrh)
    have hsum : l.numLeaves + r.numLeaves ≤ 2 ^ h + 2 ^ h :=
      Nat.add_le_add hl hr
    rw [show 2 ^ (h + 1) = 2 ^ h + 2 ^ h by omega]
    exact hsum

/-- A depth-at-most-`k` binary decision tree has at most `2^k` leaves and
`2^k - 1` internal gates. -/
theorem decisionTree_bounds {α : Type} (t : BinaryTree α) (k : ℕ)
    (hk : t.height ≤ k) :
    t.numLeaves ≤ 2 ^ k ∧ t.numNodes ≤ 2 ^ k - 1 := by
  have hleaves : t.numLeaves ≤ 2 ^ k :=
    (numLeaves_le_pow_height t).trans (Nat.pow_le_pow_right (by decide) hk)
  have hnodes_succ : t.numNodes + 1 ≤ 2 ^ k := by
    rw [← t.numLeaves_eq_numNodes_succ]
    exact hleaves
  exact ⟨hleaves, Nat.le_sub_of_add_le hnodes_succ⟩

end MathlibPlus.Combinatorics.Claim17033
