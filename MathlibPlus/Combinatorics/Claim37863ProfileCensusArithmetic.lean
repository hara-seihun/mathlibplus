import Mathlib

namespace MathlibPlus.Combinatorics.Claim37863

/--
Exact arithmetic checks for the two profile-count partitions recorded in claim
37863.  The chart, ordered-two-closure, and transporter predicates remain
outside this checksum theorem rather than being silently invented.
-/
theorem profileCensusCountChecks_claim37863 :
    (279934 : ℕ) + 2 + 0 = 279936 ∧
      (1679604 : ℕ) + 12 = 1679616 := by
  norm_num

end MathlibPlus.Combinatorics.Claim37863
