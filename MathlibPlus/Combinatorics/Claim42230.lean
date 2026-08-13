import Mathlib.Data.Set.Lattice

namespace MathlibPlus.Combinatorics.Claim42230

open Classical

/--
If each pair of carriers covers `C`, then every point of `C` belongs to at
least two carriers.  Since there are only three carriers, its multiplicity is
therefore exactly two or three.
-/
theorem carrierMultiplicity_eq_two_or_three
    {α : Type*} (C S₁ S₂ S₃ : Set α)
    (h₁₂ : S₁ ∪ S₂ = C) (h₁₃ : S₁ ∪ S₃ = C)
    (h₂₃ : S₂ ∪ S₃ = C) {y : α} (hy : y ∈ C) :
    ((if y ∈ S₁ then 1 else 0) +
        (if y ∈ S₂ then 1 else 0) +
          (if y ∈ S₃ then 1 else 0) : ℕ) = 2 ∨
      ((if y ∈ S₁ then 1 else 0) +
        (if y ∈ S₂ then 1 else 0) +
          (if y ∈ S₃ then 1 else 0) : ℕ) = 3 := by
  classical
  have hu₁₂ : y ∈ S₁ ∨ y ∈ S₂ := by
    have hy' : y ∈ S₁ ∪ S₂ := h₁₂.symm ▸ hy
    exact (Set.mem_union y S₁ S₂).mp hy'
  have hu₁₃ : y ∈ S₁ ∨ y ∈ S₃ := by
    have hy' : y ∈ S₁ ∪ S₃ := h₁₃.symm ▸ hy
    exact (Set.mem_union y S₁ S₃).mp hy'
  have hu₂₃ : y ∈ S₂ ∨ y ∈ S₃ := by
    have hy' : y ∈ S₂ ∪ S₃ := h₂₃.symm ▸ hy
    exact (Set.mem_union y S₂ S₃).mp hy'
  by_cases hs₁ : y ∈ S₁ <;>
    by_cases hs₂ : y ∈ S₂ <;>
      by_cases hs₃ : y ∈ S₃ <;>
        simp_all

end MathlibPlus.Combinatorics.Claim42230
