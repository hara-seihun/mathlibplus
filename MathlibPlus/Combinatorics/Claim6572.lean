import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Abel

namespace MathlibPlus.Combinatorics.Claim6572

/-- Translation by a fixed element preserves the Cayley relation `u - v ∈ S`. -/
theorem translation_preserves_cayley_relation
    {V : Type*} [AddCommGroup V] (S : Set V) (t : V) :
    Function.Bijective (fun u : V => u + t) ∧
      ∀ u v : V, (u + t) - (v + t) ∈ S ↔ u - v ∈ S := by
  constructor
  · constructor
    · intro x y hxy
      exact add_right_cancel hxy
    · intro y
      exact ⟨y - t, sub_add_cancel y t⟩
  · intro u v
    rw [show u + t - (v + t) = u - v by abel]

end MathlibPlus.Combinatorics.Claim6572
