import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch_019ffedc.FiniteWindowSymbols

noncomputable section

def oneVariableLaplaceSymbol (x : ℝ) (r : ℕ) (s : ℝ) : ℝ :=
  if r = 0 then
    1 - Real.exp (-x / s)
  else
    (-1 : ℝ) ^ (r - 1) * Real.exp (-x / s) / s ^ r

def adjacentDeterminantSymbol (x : ℝ) (r : ℕ) (s q : ℝ) : ℝ :=
  (oneVariableLaplaceSymbol x r s * oneVariableLaplaceSymbol x (r + 2) q +
      oneVariableLaplaceSymbol x r q * oneVariableLaplaceSymbol x (r + 2) s -
      2 * oneVariableLaplaceSymbol x (r + 1) s *
        oneVariableLaplaceSymbol x (r + 1) q) / 2

def truncatedExponential (N : ℕ) (z : ℝ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) (fun r => z ^ r / (Nat.factorial r : ℝ))

def truncatedDeterminantSymbol (N : ℕ) (x s q : ℝ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) (fun r =>
    x ^ r / (Nat.factorial r : ℝ) * adjacentDeterminantSymbol x r s q)

def zerothDeterminantSymbol : Prop :=
  ∀ (x s q : ℝ), 0 < x → 0 < s → 0 < q →
    adjacentDeterminantSymbol x 0 s q =
      -Real.exp (-x / s) / (2 * s ^ 2) -
        Real.exp (-x / q) / (2 * q ^ 2) +
        (s - q) ^ 2 / (2 * s ^ 2 * q ^ 2) *
          Real.exp (-x * (1 / s + 1 / q))

def positiveChannelDeterminantSymbol : Prop :=
  ∀ (r : ℕ) (x s q : ℝ), 1 ≤ r → 0 < x → 0 < s → 0 < q →
    adjacentDeterminantSymbol x r s q =
      (s - q) ^ 2 / (2 * s ^ (r + 2) * q ^ (r + 2)) *
        Real.exp (-x * (1 / s + 1 / q))

def completeFiniteWindowSymbol : Prop :=
  ∀ (N : ℕ) (x s q : ℝ), 0 < x → 0 < s → 0 < q →
    truncatedDeterminantSymbol N x s q =
      (s - q) ^ 2 / (2 * s ^ 2 * q ^ 2) *
          Real.exp (-x * (1 / s + 1 / q)) *
          truncatedExponential N (x / (s * q)) -
        Real.exp (-x / s) / (2 * s ^ 2) -
        Real.exp (-x / q) / (2 * q ^ 2)

def positiveOrderAndMicroscopicDecompositions : Prop :=
  ∀ (N : ℕ) (x s q : ℝ), 1 ≤ N → 0 < x → 0 < s → 0 < q →
    (Finset.sum (Finset.Icc 1 N) (fun r =>
      x ^ r / (Nat.factorial r : ℝ) * adjacentDeterminantSymbol x r s q)) =
        (s - q) ^ 2 / (2 * s ^ 2 * q ^ 2) *
          Real.exp (-x * (1 / s + 1 / q)) *
          (truncatedExponential N (x / (s * q)) - 1) ∧
    (Finset.sum (Finset.Icc 2 N) (fun r =>
      x ^ r / (Nat.factorial r : ℝ) * adjacentDeterminantSymbol x r s q)) =
        (s - q) ^ 2 / (2 * s ^ 2 * q ^ 2) *
          Real.exp (-x * (1 / s + 1 / q)) *
          (truncatedExponential N (x / (s * q)) - 1 - x / (s * q))

end
end MathlibPlus.Open.Research.FormalizationBatch_019ffedc.FiniteWindowSymbols
