import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2614

noncomputable section

open Polynomial

/-- The coefficient kernel with its polynomial carrier and the zero extension
needed for the lowered row q-1. -/
def kernelRowNat42805 (R q j : ℕ) : ℚ :=
  ((1 + 2 * X) * X ^ j * (1 + X) ^ (R + j - 1 : ℕ)).coeff q

def kernelRowInt42805 (R : ℕ) (q : ℤ) (j : ℕ) : ℚ :=
  if q < 0 then 0 else kernelRowNat42805 R q.toNat j

def weightedRowTransform42805 (R q j : ℕ) : ℚ :=
  ((R + q : ℕ) : ℚ) * kernelRowInt42805 R ((q : ℤ) - 1) j -
    kernelRowInt42805 R q j

def weightedRowFormula42805 (R q j : ℕ) : ℚ :=
  let n := R + j
  let k := q - j
  (((n + k : ℕ) : ℚ) * ((k : ℚ) - 1) *
      ((n + k + 1 : ℕ) : ℚ)) /
    ((n : ℚ) * ((n - k + 1 : ℕ) : ℚ)) *
    (Nat.choose n k : ℚ)

/-- Claim 42805: the actual coefficient-kernel row transform has the stated
n=R+j, k=q-j formula on its supported domain, with the complete sign and
endpoint classification. -/
def claim42805 : Prop :=
  (∀ (R q j : ℕ),
    1 ≤ R → j ≤ q → q ≤ R + 2 * j →
      weightedRowTransform42805 R q j =
        weightedRowFormula42805 R q j ∧
      (j + 2 ≤ q → 0 < weightedRowTransform42805 R q j) ∧
      (q = j + 1 → weightedRowTransform42805 R q j = 0) ∧
      (q = j → weightedRowTransform42805 R q j = -1)) ∧
    (∀ (R q j : ℕ), 1 ≤ R → q < j →
      weightedRowTransform42805 R q j = 0)

end

end MathlibPlus.Open.ResearchFormalization.R2614
