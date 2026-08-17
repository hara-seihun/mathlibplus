import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3748

noncomputable section

abbrev Outcome := Bool × Bool

def sign (b : Bool) : ℝ :=
  if b then 1 else -1

def targetValue (o : Outcome) : ℝ :=
  sign o.2

def noRepeatPolicy : Fin 2 → Fin 2 :=
  fun i => i

def meanTwo (f : Bool → ℝ) : ℝ :=
  (f false + f true) / 2

def varianceFour (f : Outcome → ℝ) : ℝ :=
  let μ :=
    (f (false, false) + f (false, true) +
      f (true, false) + f (true, true)) / 4
  ((f (false, false) - μ) ^ 2 +
    (f (false, true) - μ) ^ 2 +
    (f (true, false) - μ) ^ 2 +
    (f (true, true) - μ) ^ 2) / 4

def posteriorVarianceAfterFirst (b : Bool) : ℝ :=
  let μ := meanTwo (fun c => targetValue (b, c))
  ((targetValue (b, false) - μ) ^ 2 +
    (targetValue (b, true) - μ) ^ 2) / 2

def posteriorVarianceAt (m : Fin 3) : ℝ :=
  match m.1 with
  | 0 => varianceFour targetValue
  | 1 =>
      (posteriorVarianceAfterFirst false +
        posteriorVarianceAfterFirst true) / 2
  | _ => 0

def truePosteriorArea : ℝ :=
  posteriorVarianceAt 0 + posteriorVarianceAt 1 + posteriorVarianceAt 2

def separationTime (u v : Outcome) : ℕ :=
  if u.1 = v.1 then 2 else 1

def pairTerm (m : ℕ) (u v : Outcome) : ℝ :=
  (targetValue u - targetValue v) ^ 2 *
    if separationTime u v > m then 1 else 0

def pairAverage (f : Outcome → Outcome → ℝ) : ℝ :=
  (∑ u : Outcome, ∑ v : Outcome, f u v) / 16

def claimedLinearPairArea : ℝ :=
  (pairAverage (pairTerm 0) + pairAverage (pairTerm 1)) / 2

/-- Claim 49433: the fixed two-bit no-repeat policy has true posterior
variance area `2`, while the claimed prior-pair linear expression is `3/2`. -/
def claim49433_falseLinearPairOccupationIdentity : Prop :=
  noRepeatPolicy 0 = 0 ∧
    noRepeatPolicy 1 = 1 ∧
    truePosteriorArea = 2 ∧
      claimedLinearPairArea = 3 / 2 ∧
        truePosteriorArea ≠ claimedLinearPairArea

end
end MathlibPlus.Open.ResearchFormalization.R3748
