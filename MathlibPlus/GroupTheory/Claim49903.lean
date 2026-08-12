import Mathlib

namespace MathlibPlus.GroupTheory

/-- The two order-four square roots of one fixed-point-free involution on four
points generate the same cyclic subgroup.  This is the exact finite block
calculation used by claim 49903. -/
theorem squareRootSubgroup_eq_claim49903
    (r t δ : Equiv.Perm (Fin 4))
    (hr : r ^ 4 = 1 ∧ r ^ 2 ≠ 1)
    (ht : t ^ 4 = 1 ∧ t ^ 2 ≠ 1)
    (_hδ : ∀ x, δ x ≠ x)
    (hrδ : r ^ 2 = δ)
    (htδ : t ^ 2 = δ) :
    Subgroup.closure ({r} : Set (Equiv.Perm (Fin 4))) =
      Subgroup.closure ({t} : Set (Equiv.Perm (Fin 4))) := by
  clear _hδ
  have hroot : t = r ∨ t = r⁻¹ := by
    by_cases htr : t = r
    · exact Or.inl htr
    · right
      native_decide +revert
  rcases hroot with rfl | rfl
  · rfl
  · exact (Subgroup.closure_singleton_inv r).symm

end MathlibPlus.GroupTheory
