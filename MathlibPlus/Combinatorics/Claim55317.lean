import Mathlib

namespace MathlibPlus.Combinatorics.Claim55317

noncomputable section

/-- The coefficient triangle from the shifted-cycle recurrence.  Values with
`k > n` are the stipulated zero-outside-the-valid-range values. -/
def shiftedCycleCoeff (r n k : ℕ) : ℕ :=
  if n = 0 then
    if k = 0 then 1 else 0
  else if n < k then 0
  else
    Nat.factorial (r - 1) * (n + (r - 1) * k - 1).choose (r - 1) *
        (if k = 0 then 0 else shiftedCycleCoeff r (n - 1) (k - 1)) +
      (n + (r - 1) * k - 1) * shiftedCycleCoeff r (n - 1) k
termination_by n

def shiftedCyclePolynomial (r n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (shiftedCycleCoeff r n k : ℤ) * Polynomial.X ^ k

theorem shiftedCycleCoeff_zero_outside (r n k : ℕ) (hk : n < k) :
    shiftedCycleCoeff r n k = 0 := by
  unfold shiftedCycleCoeff
  split <;> rename_i h
  · split <;> simp_all
  · simp

theorem shiftedCycleCoeff_base (r k : ℕ) (hk : k ≠ 0) :
    shiftedCycleCoeff r 0 k = 0 := by
  simp [shiftedCycleCoeff, hk]

theorem shiftedCycleCoeff_recurrence
    (r n k : ℕ) (_hr : 3 ≤ r) (hn : 0 < n) (hk : k ≤ n) :
    shiftedCycleCoeff r n k =
      Nat.factorial (r - 1) * (n + (r - 1) * k - 1).choose (r - 1) *
          (if k = 0 then 0 else shiftedCycleCoeff r (n - 1) (k - 1)) +
        (n + (r - 1) * k - 1) * shiftedCycleCoeff r (n - 1) k := by
  rw [shiftedCycleCoeff]
  simp only [if_neg (Nat.ne_of_gt hn), if_neg (Nat.not_lt_of_ge hk)]

end

end MathlibPlus.Combinatorics.Claim55317
