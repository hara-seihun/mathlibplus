import MathlibPlus.Basic

namespace MathlibPlus.Algebra

open fwdDiff

/-- The unit-step forward-difference expansion underlying the divided-difference
identity in claim 1085.  The source does not define a separate carrier for
`A_{k,j}`, so the left side explicitly records its normalized binomial sum. -/
theorem dividedDifferenceIdentity_claim1085 (k j : ℕ) (a : ℚ) :
    let A : ℚ :=
      (1 / (Nat.factorial k : ℚ)) *
        ∑ r ∈ Finset.range (k + 2),
          ((((-1 : ℤ) ^ (k + 1 - r) * (k + 1).choose r : ℤ) : ℚ) *
            (a + (r : ℚ)) ^ (2 * j))
    A = (1 / (Nat.factorial k : ℚ)) *
      (fwdDiff (1 : ℚ))^[k + 1] (fun x : ℚ => x ^ (2 * j)) a := by
  dsimp
  have h := fwdDiff_iter_eq_sum_shift (h := (1 : ℚ))
    (f := fun x : ℚ => x ^ (2 * j)) (n := k + 1) (y := a)
  have hscaled := congrArg
    (fun z : ℚ => (1 / (Nat.factorial k : ℚ)) * z) h
  simpa [smul_eq_mul] using hscaled.symm

end MathlibPlus.Algebra
