import Mathlib
import MathlibPlus.Open.C0079NeighboringMinor

open scoped BigOperators

namespace MathlibPlus.Open.C0079Claim1187

noncomputable section

/-- The flagged entry, with the packet's zero extension for negative degrees. -/
def flaggedEntry1187 (a : ℚ) (k j : ℕ) : ℚ :=
  (k + 1 : ℚ) *
    MathlibPlus.Open.C0079.completeHomogeneousInt
      (2 * (j : ℤ) - (k : ℤ) - 1)
      (k + 2)
      (MathlibPlus.Open.C0079.consecutiveVariables a k)

/-- The padded-partition row index used by the flagged minors. -/
def partitionRow1187 (parts : List ℕ) (d : ℕ) (i : Fin d) : ℕ :=
  i.1 + parts.getD (d - 1 - i.1) 0

/-- The determinant carrier for a partition-indexed flagged minor. -/
def flaggedMinor1187 (parts : List ℕ) (d : ℕ) (a : ℚ) : ℚ :=
  Matrix.det (fun (i : Fin d) (j : Fin d) =>
    flaggedEntry1187 a (partitionRow1187 parts d i) (j.1 + 1))

def emptyMinor1187 (d : ℕ) (a : ℚ) : ℚ :=
  flaggedMinor1187 [] d a

def oneOneOneMinor1187 (d : ℕ) (a : ℚ) : ℚ :=
  flaggedMinor1187 [1, 1, 1] d a

/-- Claim 1187, with ordinary quotient semantics away from the principal and
 displayed denominator zeros and the everywhere cross-multiplied identity. -/
def claim1187 : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ a : ℚ,
    let y : ℚ := 2 * a + (d : ℚ)
    let denominator : ℚ := 6 * (y - 2) * (y - 1) * y
    let numerator : ℚ :=
      ((d : ℚ) + 1) * ((d : ℚ) + 2) * ((d : ℚ) + 3)
    let hEmpty : ℚ := emptyMinor1187 d a
    let hOneOneOne : ℚ := oneOneOneMinor1187 d a
    (hEmpty ≠ 0 ∧ denominator ≠ 0 →
      hOneOneOne / hEmpty = numerator / denominator) ∧
    denominator * hOneOneOne = numerator * hEmpty ∧
    (d = 3 →
      let denominator3 : ℚ := (y - 2) * (y - 1) * y
      (hEmpty ≠ 0 ∧ denominator3 ≠ 0 →
        hOneOneOne / hEmpty = 20 / denominator3))

end

end MathlibPlus.Open.C0079Claim1187
