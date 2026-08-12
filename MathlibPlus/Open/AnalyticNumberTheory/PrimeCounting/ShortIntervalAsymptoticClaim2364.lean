import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

open Filter Asymptotics

/-- Claim 2364: for every exponent above 7/12, the prime-counting increment
across an interval of length x^θ is asymptotic to x^θ / log x.  The second
conjunct records the stated θ = 3/5 reflected-interval consequence. -/
def shortIntervalPrimeAsymptotic_claim2364 : Prop :=
  (∀ θ : ℝ, (7 / 12 : ℝ) < θ →
    (fun x : ℝ =>
      (Nat.primeCounting (Nat.floor (x + Real.rpow x θ)) : ℝ) -
        Nat.primeCounting (Nat.floor x)) ~[atTop]
      (fun x : ℝ => Real.rpow x θ / Real.log x)) ∧
    Tendsto (fun c : ℝ =>
      (Nat.primeCounting (Nat.floor c) : ℝ) -
        Nat.primeCounting (Nat.floor (c - Real.rpow c (3 / 5 : ℝ)))) atTop atTop

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
