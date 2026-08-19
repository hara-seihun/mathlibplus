import MathlibPlus.Open.C0079AreaThreeCoordinates

namespace MathlibPlus.Open.C0079

open scoped BigOperators

noncomputable section

/-- The `(2,1)` signed flagged-minor combination in the packet's gauged cup
coordinate convention. -/
def alphaTwoOne1182 (d : ℕ) (hd : 2 ≤ d) (a : ℝ) : ℝ :=
  let hd1 : 1 ≤ d := Nat.le_trans
    (Nat.succ_le_succ (Nat.zero_le 1)) hd
  2 * emptyMinor d a - flaggedMinorRows1181 d a (oneRows1181 d hd1) +
      flaggedMinorRows1181 d a (twoRows1181 d hd) +
      flaggedMinorRows1181 d a (oneOneRows1181 d hd) -
        flaggedMinorRows1181 d a (twoOneRows1181 d hd)

/-- The numerator polynomial displayed for the area-three `(2,1)` coordinate. -/
def numeratorTwoOne1182 (d : ℕ) (b : ℝ) : ℝ :=
  48 * b ^ 3 +
    60 * ((d : ℝ) + 1) * b ^ 2 +
    6 * (5 * (d : ℝ) ^ 2 + 10 * (d : ℝ) + 2) * b +
    5 * (d : ℝ) ^ 3 + 15 * (d : ℝ) ^ 2 + 16 * (d : ℝ) + 12

/-- Claim 1182: the exact area-three `(2,1)` cup coordinate, with the
ordinary quotient assertion away from denominator zeros and its everywhere
cross-multiplied form. -/
def claim1182 : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (a : ℝ),
    let b : ℝ := a - 1 / 2
    let x : ℝ := x1181 d b
    let numerator : ℝ := numeratorTwoOne1182 d b * principalProduct1181 d b
    let denominator : ℝ := 3 * (x - 1) * x * (x + 1)
    (denominator ≠ 0 → alphaTwoOne1182 d hd a = numerator / denominator) ∧
      denominator * alphaTwoOne1182 d hd a = numerator

end

end MathlibPlus.Open.C0079
