import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Fintype.BigOperators

namespace MathlibPlus.Algebra

/-- Claim 32421: over characteristic two, a finite multiplicity-weighted
child sum depends only on each child's multiplicity modulo two. -/
theorem childParityWeightedSum_claim32421
    {R α : Type*} [Semiring R] [CharP R 2] [Fintype α]
    (Λ : α → R) (m n : α → ℕ)
    (hparity : ∀ a : α, m a % 2 = n a % 2) :
    (∑ a : α, (m a : R) * Λ a) =
      ∑ a : α, (n a : R) * Λ a := by
  apply Fintype.sum_congr
  intro a
  have hcast : (m a : R) = (n a : R) := by
    rw [← Nat.mod_add_div (m a) 2, ← Nat.mod_add_div (n a) 2, hparity a]
    have htwo : (2 : R) = 0 := CharP.cast_eq_zero R 2
    simp [htwo]
  rw [hcast]

end MathlibPlus.Algebra
