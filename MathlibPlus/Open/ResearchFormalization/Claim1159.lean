import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim1159

noncomputable section

/-- Complete homogeneous symmetric evaluation on a finite consecutive list. -/
def completeHomogeneous (n : ℕ) : List ℝ → ℝ
  | [] => if n = 0 then 1 else 0
  | x :: xs =>
      ∑ i ∈ Finset.range (n + 1),
        x ^ i * completeHomogeneous (n - i) xs
termination_by xs => xs.length

/-- The flagged complete-homogeneous array from the shared setup. -/
def flaggedArrayEntry (a : ℝ) (k j : ℕ) : ℝ :=
  if k + 1 ≤ 2 * j then
    (k + 1 : ℝ) *
      completeHomogeneous (2 * j - k - 1)
        (List.map (fun n => a + n) (List.range (k + 2)))
  else 0

/-- A flagged maximal minor selected by an explicit row list. -/
def flaggedMinorFromRows (a : ℝ) (rows : Fin d → ℕ) : ℝ :=
  Matrix.det (fun i j => flaggedArrayEntry a (rows i) (j.1 + 1))

/-- The principal row set and its flagged minor. -/
def principalRows (d : ℕ) (i : Fin d) : ℕ := i.1

def principalFlaggedMinor (a : ℝ) (d : ℕ) : ℝ :=
  flaggedMinorFromRows a (principalRows d)

/-- The rows for the partitions `(1)`, `(2)`, and `(1,1)`. -/
def oneRows (d : ℕ) (i : Fin d) : ℕ :=
  if i.1 = d - 1 then d else i.1

def twoRows (d : ℕ) (i : Fin d) : ℕ :=
  if i.1 = d - 1 then d + 1 else i.1

def oneOneRows (d : ℕ) (i : Fin d) : ℕ :=
  if i.1 = d - 2 then d - 1 else if i.1 = d - 1 then d else i.1

def oneFlaggedMinor (a : ℝ) (d : ℕ) : ℝ :=
  flaggedMinorFromRows a (oneRows d)

def twoFlaggedMinor (a : ℝ) (d : ℕ) : ℝ :=
  flaggedMinorFromRows a (twoRows d)

def oneOneFlaggedMinor (a : ℝ) (d : ℕ) : ℝ :=
  flaggedMinorFromRows a (oneOneRows d)

/-- Exact adjacent flagged-minor ratios, with cross-multiplied identities at
roots of the principal minor or visible denominator. -/
def exactAdjacentFlaggedMinorRatios_claim1159 : Prop :=
  (∀ d : ℕ, 1 ≤ d → ∀ a : ℝ,
      let Y : ℝ := 2 * a + d
      (principalFlaggedMinor a d ≠ 0 → Y ≠ 0 →
        oneFlaggedMinor a d / principalFlaggedMinor a d =
          ((d + 1 : ℕ) : ℝ) / Y) ∧
      Y * oneFlaggedMinor a d =
        ((d + 1 : ℕ) : ℝ) * principalFlaggedMinor a d) ∧
  (∀ d : ℕ, 2 ≤ d → ∀ a : ℝ,
      let Y : ℝ := 2 * a + d
      (principalFlaggedMinor a d ≠ 0 → 2 * Y * (Y + 1) ≠ 0 →
        twoFlaggedMinor a d / principalFlaggedMinor a d =
          (((d - 1) * (d + 2) : ℕ) : ℝ) / (2 * Y * (Y + 1))) ∧
      2 * Y * (Y + 1) * twoFlaggedMinor a d =
        (((d - 1) * (d + 2) : ℕ) : ℝ) * principalFlaggedMinor a d) ∧
  (∀ d : ℕ, 2 ≤ d → ∀ a : ℝ,
      let Y : ℝ := 2 * a + d
      (principalFlaggedMinor a d ≠ 0 → 2 * Y * (Y - 1) ≠ 0 →
        oneOneFlaggedMinor a d / principalFlaggedMinor a d =
          (((d + 1) * (d + 2) : ℕ) : ℝ) / (2 * Y * (Y - 1))) ∧
      2 * Y * (Y - 1) * oneOneFlaggedMinor a d =
        (((d + 1) * (d + 2) : ℕ) : ℝ) * principalFlaggedMinor a d)

end

end MathlibPlus.Open.ResearchFormalization.Claim1159
