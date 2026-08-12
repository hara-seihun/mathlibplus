import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/-- Claim 5465: strict descent makes selected rows distinct.

The incidence relation says which columns occur in which rows.  The strict-descent
hypothesis says that every other column in a column's selected row has strictly
smaller wave; this simultaneously excludes equal-wave ties and lower-wave columns
appearing in the selected row of a higher-wave column. -/
theorem selectedRows_injective_claim5465
    {C R W : Type*} [PartialOrder W]
    (selected : C → R) (wave : C → W) (incident : C → R → Prop)
    (h_selected : ∀ c, incident c (selected c))
    (h_strict : ∀ c d, c ≠ d → incident d (selected c) → wave d < wave c) :
    Function.Injective selected := by
  intro c d hcd
  by_contra hne
  have hdc : d ≠ c := Ne.symm hne
  have h₁ : wave d < wave c := by
    apply h_strict c d hne
    rw [hcd]
    exact h_selected d
  have h₂ : wave c < wave d := by
    apply h_strict d c hdc
    rw [← hcd]
    exact h_selected c
  exact (not_lt_of_ge (le_of_lt h₂)) h₁

end MathlibPlus.Combinatorics
