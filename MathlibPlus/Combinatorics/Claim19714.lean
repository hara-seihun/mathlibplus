import Mathlib

namespace MathlibPlus.Combinatorics

/-- The exact binomial-count core of admitted claim 19714.  The source's
profile parameters are not introduced here because their ambient profile type
is not specified in the claim packet. -/
theorem claim19714_excessProfileCount (r : ℕ) :
    (∑ j ∈ Finset.range (r + 1), Nat.choose (j + 3) 3) =
      Nat.choose (r + 4) 4 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show r + 1 + 3 = r + 4 by omega]
    have h := Nat.choose_succ_succ (r + 4) 3
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

end MathlibPlus.Combinatorics
