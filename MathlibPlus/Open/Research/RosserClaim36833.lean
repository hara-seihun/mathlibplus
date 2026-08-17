import MathlibPlus.Open.Research.Rosser

noncomputable section
open scoped BigOperators
open Classical

namespace MathlibPlus.Open.Research.Rosser

/-- The interval floor remainder used at the universal maximizing shift. -/
def floorRemainder (d H : ℕ) (t : ℝ) : ℝ :=
  (Int.floor ((t + (H : ℝ)) / (d : ℝ)) : ℝ) -
    (Int.floor (t / (d : ℝ)) : ℝ) - (H : ℝ) / (d : ℝ)

/-- The signed lower-Rosser remainder at the shift `-1`, using the exact
support and integer Möbius weights from the admitted lower-support carrier. -/
def signedLowerRemainder (D z H : ℕ) : ℝ :=
  ∑ d ∈ rosserLowerSupport D z,
    (rosserLowerWeight D z d : ℝ) * floorRemainder d H (-1)

/-- Claim 36833: the individual floor remainders are maximized at `-1`, the
exact Rosser signs cancel their constant component, and pairing each odd
support element with its toggle-two partner gives the stated factor-four
bound for every positive interval length. -/
def claim36833 : Prop :=
  ∀ D z : ℕ, 64 ≤ D → 2 < z → z ≤ Nat.sqrt D →
    ∀ H : ℕ, 0 < H →
      (∀ d ∈ rosserLowerSupport D z, 0 < d →
        ∀ t : ℝ, floorRemainder d H t ≤ floorRemainder d H (-1)) ∧
      (∑ d ∈ rosserLowerSupport D z,
        (rosserLowerWeight D z d : ℝ)) = 0 ∧
      (∀ d ∈ rosserLowerSupport D z, Odd d →
        |floorRemainder d H (-1) -
            floorRemainder (2 * d) H (-1)| ≤ (1 : ℝ) / 2) ∧
      |signedLowerRemainder D z H| ≤
        (1 : ℝ) / 4 * (rosserLowerSupport D z).card

end MathlibPlus.Open.Research.Rosser
