import Mathlib

namespace MathlibPlus.Algebra.InfiniteRankFeasibility

/-- The infinite-rank base domain associated with a family of finite-rank
base domains. -/
def infiniteRankBaseDomain {α : Type*} (D : ℕ → Set α) : Set α :=
  ⋂ N, D N

/-- The infinite-rank base domain is the displayed intersection of all
finite-rank base domains. -/
theorem infiniteRankBaseDomain_eq_iInter
    {α : Type*} (D : ℕ → Set α) :
    infiniteRankBaseDomain D = ⋂ N, D N := by
  rfl

/-- Feasibility in the infinite-rank base domain is membership in every
finite-rank base domain in the family. -/
theorem mem_infiniteRankBaseDomain_iff
    {α : Type*} (D : ℕ → Set α) (x : α) :
    x ∈ infiniteRankBaseDomain D ↔ ∀ N, x ∈ D N := by
  simp [infiniteRankBaseDomain]

end MathlibPlus.Algebra.InfiniteRankFeasibility
