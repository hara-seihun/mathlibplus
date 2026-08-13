import Mathlib

namespace MathlibPlus.Combinatorics

/-- The additive defect of a finite multiset of natural part sizes, namely
    the sum of one less than each part.  A natural partition is represented
    extensionally by its multiset of parts. -/
def componentPartitionDefect_claim24789 (parts : Multiset ℕ) : ℕ :=
  (parts.map (fun a => a - 1)).sum

end MathlibPlus.Combinatorics
