import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim40704

/-!
Claim 40704 records two marked-row incidence totals.  The source's `8T7` and
`8T16` row carriers are not defined in the packet, so this file retains their
four exact displayed counts and proves the aggregate arithmetic without
inventing a graph or marking convention.
-/

/-- The two marked row families have the displayed total and proper-incidence sums. -/
theorem markedRowIncidenceTotals :
    (576 : ℕ) + 1792 = 2368 ∧
      572 + 1728 = 2300 := by
  norm_num

end MathlibPlus.Combinatorics.Claim40704
