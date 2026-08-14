import Mathlib

noncomputable section

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
# Prime-interval bridges and the first theta envelope, claims 948--950

The order-three/order-four and order-four/order-five interval statements are
written with their source coefficients inlined.  The first theta-envelope
node keeps the two-sided relative-error carrier and the non-prime endpoint
explicit, including the continuity step used to close the half-line bound.
-/

/-- Claim 948: the order-three interval theorem from `17051708` transfers to
order four with coefficient `B₄` up to the displayed logarithmic ratio. -/
def orderThreeToFourBridge_claim948 : Prop :=
  let A₃ : ℝ := 486680000822 / 10000000000000
  let B₄ : ℝ := (34 / 1327 : ℝ) * (Real.log 1327) ^ 4
  let ratio : ℝ := B₄ / A₃
  (1407483734849 : ℝ) / 1000000000 ≤ ratio ∧
    ratio < (1407483734850 : ℝ) / 1000000000 ∧
    (∀ x : ℝ, 17051708 ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x * (1 + A₃ / (Real.log x) ^ 3)) ∧
    (∀ x : ℝ, 17051708 ≤ x → Real.log x ≤ ratio →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x * (1 + B₄ / (Real.log x) ^ 4))

/-- Claim 949: the order-four interval theorem transfers into the order-five
`B₅` interval through the displayed logarithmic ratio. -/
def orderFourToFiveBridge_claim949 : Prop :=
  let B₄ : ℝ := (34 / 1327 : ℝ) * (Real.log 1327) ^ 4
  let B₅ : ℝ := 252969215940000000000 / 1999999999996903
  let ratio : ℝ := B₅ / B₄
  (1846506301759 : ℝ) / 1000000000 ≤ ratio ∧
    ratio < (1846506301760 : ℝ) / 1000000000 ∧
    (∀ x : ℝ, 2 ≤ x →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x * (1 + B₄ / (Real.log x) ^ 4)) ∧
    (∀ x : ℝ, 2 ≤ x → Real.log x ≤ ratio →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x * (1 + B₅ / (Real.log x) ^ 5))

/-- Claim 950: the corrected two-sided relative theta error at the first
logarithmic endpoint has the stated directed decimal enclosure, and the
outward-rounded half-line bound closes at that endpoint because the endpoint
is not prime. -/
def correctedFirstNumericalThetaEnvelope_claim950 : Prop :=
  let x₀ : ℝ := 10 ^ 19
  let L₀ : ℝ := 19 * Real.log 10
  let E : ℝ → ℝ := fun L =>
    |Chebyshev.theta (Real.exp L) - Real.exp L| / Real.exp L
  let εout : ℝ := 19537 / 1000000000000
  L₀ = Real.log x₀ ∧
    (1953644927822 : ℝ) / 100000000000000000000 ≤ E L₀ ∧
    E L₀ < (1953644927823 : ℝ) / 100000000000000000000 ∧
    E L₀ < εout ∧
    ContinuousAt E L₀ ∧
    (∀ L : ℝ, L₀ < L → E L ≤ εout) ∧
    ¬ Nat.Prime (10 ^ 19)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
