import Mathlib

namespace MathlibPlus.Combinatorics.Claim5540

/-- In an acyclic dependency relation, selectors cannot assign one row to two
 distinct columns when that collision creates both directed edges. -/
theorem acyclicIncidentSelectorsInjective_claim5540
    {α β : Type*}
    (select : α → β)
    (edge : α → α → Prop)
    (hacyclic : ∀ c, ¬ Relation.TransGen edge c c)
    (hcycle : ∀ c d, c ≠ d → select c = select d → edge c d ∧ edge d c) :
    Function.Injective select := by
  intro c d hsel
  by_contra hne
  have hedges := hcycle c d hne hsel
  exact hacyclic c (Relation.TransGen.head hedges.1 (Relation.TransGen.single hedges.2))

end MathlibPlus.Combinatorics.Claim5540
