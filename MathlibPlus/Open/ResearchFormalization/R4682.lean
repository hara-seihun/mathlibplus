import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

def threeCyclicPeriod : Set (ZMod 9) :=
  {x | ∃ k : ZMod 9, x = 3 • k}

def normalizedC3ToC9 (q : ZMod 3) : ZMod 9 :=
  (q.val : ZMod 9)

/-- R-4682, S3: on C9 the period-three congruences hold for the displayed
normalized transporter, but no common order-three shadow exists. -/
def claim54015 : Prop :=
  let P : Set (ZMod 9) := threeCyclicPeriod
  let c : ZMod 3 → ZMod 9 := normalizedC3ToC9
  c 0 = 0 ∧ c 1 = 1 ∧ c 2 = 2 ∧
    (∀ b : ZMod 3, ∀ q : ZMod 3,
      (q = 1 ∨ q = 2) → c (b + q) - c b - c q ∈ P) ∧
    ¬∃ a : ZMod 9,
      3 • a = 0 ∧ c 1 - a ∈ P ∧ c 2 - 2 • a ∈ P

end

end MathlibPlus.Open.ResearchFormalization
