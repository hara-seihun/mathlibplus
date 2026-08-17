import MathlibPlus.Open.C0079NeighboringMinor

namespace MathlibPlus.Open.C0079

/-- The exact flagged-array entry on the finite row and column carriers. -/
def flaggedArrayEntry1178 (d : ℕ) (a : ℝ) (k : Fin (2 * d)) (j : Fin d) : ℝ :=
  ((k.1 + 1 : ℕ) : ℝ) *
    completeHomogeneousInt
      ((2 : ℤ) * ((j.1 + 1 : ℕ) : ℤ) - (k.1 : ℤ) - 1)
      (k.1 + 2) (consecutiveVariables a k.1)

/-- Claim 1178: the finite flagged array is the stated complete-homogeneous
array, with `d = r - 1` and the one-based column index encoded by `Fin d`. -/
def claim1178 : Prop :=
  ∀ (r : ℕ), 2 ≤ r →
    ∀ (a : ℝ) (k : Fin (2 * (r - 1))) (j : Fin (r - 1)),
      flaggedArray (r - 1) a k j =
        ((k.1 + 1 : ℕ) : ℝ) *
          completeHomogeneousInt
            ((2 : ℤ) * ((j.1 + 1 : ℕ) : ℤ) - (k.1 : ℤ) - 1)
            (k.1 + 2) (consecutiveVariables a k.1)

end MathlibPlus.Open.C0079
