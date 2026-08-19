import Mathlib
import MathlibPlus.Open.ResearchFormalization.C0102C0119Batch

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0110Claim1708

open MathlibPlus.Open.ResearchFormalization.C0102C0119

noncomputable section

/-- The selected row tuple for the padded partition `(n,3)`. -/
def thirdStripRows1708 (d n : ℕ) : Fin d → ℕ :=
  fun i =>
    if i.1 < d - 2 then i.1
    else if i.1 = d - 2 then d + 1
    else d + n - 1

/-- The principal and `(n,3)` flagged minors. -/
def principalMinor1708 (a : ℝ) (d : ℕ) : ℝ :=
  flaggedMinor a d (fun i => i.1)

def thirdStripMinor1708 (a : ℝ) (d n : ℕ) : ℝ :=
  flaggedMinor a d (thirdStripRows1708 d n)

/-- The half-shifted value of `Y=2a+d`. -/
def y1708 (b : ℝ) (d : ℕ) : ℝ :=
  2 * b + (d : ℝ) + 1

/-- Rising factorial `x (x+1) ... (x+k-1)`. -/
def rising1708 (x : ℝ) (k : ℕ) : ℝ :=
  ∏ r ∈ Finset.range k, (x + (r : ℝ))

/-- The exact third-strip amplitude `Z_n(d)`. -/
def z1708 (d n : ℕ) : ℝ :=
  (((d : ℝ) + 2) * ((d : ℝ) + (n : ℝ)) * ((n : ℝ) - 2) *
      ((d : ℝ) ^ 2 + (d : ℝ) - 3 * (n : ℝ) - 3) *
      Finset.prod (Finset.Icc 1 (n - 1)) (fun r =>
        (d : ℝ) - (r : ℝ))) /
    (6 * (Nat.factorial (n + 1) : ℝ))

/-- The nonnegative numerator-factor assertion in the stated domain. -/
def zFactorsNonnegative1708 (d n : ℕ) : Prop :=
  0 ≤ (d : ℝ) + 2 ∧
    0 ≤ (d : ℝ) + (n : ℝ) ∧
    0 ≤ (n : ℝ) - 2 ∧
    0 ≤ (d : ℝ) ^ 2 + (d : ℝ) - 3 * (n : ℝ) - 3 ∧
    (∀ r ∈ Finset.Icc 1 (n - 1), 0 ≤ (d : ℝ) - (r : ℝ))

/-- Claim 1708: the exact neighboring-minor ratio for the `(n,3)` row,
without restricting the half-shift variable, together with the stated
amplitude positivity and factor signs. -/
def claim1708 : Prop :=
  (∀ (b : ℝ) (n d : ℕ),
    3 ≤ n → max n 4 ≤ d →
      thirdStripMinor1708 (b + 1 / 2) d n /
          principalMinor1708 (b + 1 / 2) d =
        z1708 d n /
          (y1708 b d * (y1708 b d + 1) *
            rising1708 (y1708 b d - 1) (n + 1))) ∧
  (∀ (n d : ℕ),
    3 ≤ n → max n 4 ≤ d →
      zFactorsNonnegative1708 d n ∧ 0 < z1708 d n)

end

end MathlibPlus.Open.ResearchFormalization.C0110Claim1708
