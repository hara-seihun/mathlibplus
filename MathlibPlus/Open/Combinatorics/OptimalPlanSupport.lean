import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The optimal integral transport plans are exactly the feasible plans supported
    on entries used by some optimal plan. -/
def optimalPlanSupportCharacterization
    (L R : Type*) [Fintype L] [Fintype R]
    (e : L → ℕ) (b : R → ℕ) (c : L → R → ℤ)
    (h_mass : (∑ i, e i) = (∑ j, b j)) : Prop :=
  let Plan : Set (L → R → ℕ) :=
    {x | (∀ i, ∑ j, x i j = e i) ∧ (∀ j, ∑ i, x i j = b j)}
  let cost : (L → R → ℕ) → ℤ :=
    fun x => ∑ i, ∑ j, (c i j) * (x i j : ℤ)
  let P_opt : Set (L → R → ℕ) :=
    {x | x ∈ Plan ∧ ∀ y, y ∈ Plan → cost x ≤ cost y}
  let Z : Set (L × R) :=
    {p | ∃ x, x ∈ P_opt ∧ 0 < x p.1 p.2}
  P_opt = {x | x ∈ Plan ∧ ∀ i j, x i j > 0 → (i, j) ∈ Z}

end MathlibPlus.Open.Combinatorics
