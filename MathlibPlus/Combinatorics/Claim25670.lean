import Mathlib.Tactic

namespace MathlibPlus.Combinatorics.Claim25670

/-- The signature identity from packet R-0369.  The packet's
majority-heavy/proper-principal-root conditions determine the set `R` but are
not used by this order-theoretic identity, so `R` is retained as an arbitrary
set of support nodes rather than replaced by an invented profile interface. -/
theorem majorityHeavySignature_join
    {α : Type*} [SemilatticeSup α] (R : Set α) (x y : α) :
    let sigma : α → Set α := fun s => {r | r ∈ R ∧ ¬ s ≤ r}
    sigma (x ⊔ y) = sigma x ∪ sigma y := by
  dsimp
  ext r
  by_cases hx : x ≤ r <;> by_cases hy : y ≤ r <;>
    simp [sup_le_iff, hx, hy]

end MathlibPlus.Combinatorics.Claim25670
