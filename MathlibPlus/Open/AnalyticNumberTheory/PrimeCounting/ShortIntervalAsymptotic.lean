import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

open Filter Asymptotics

/-!
Formalization of admitted claim 2326 (locator `C-0147`).  The source writes
`π(x)` for the prime-counting function on real arguments; here it is made
explicit as `Nat.primeCounting (Nat.floor x)`.  The reflection sentence is
represented by the corresponding endpoint difference at the special exponent
`3/5`; endpoint and floor conventions are therefore visible to fidelity review.
-/

/-- Short intervals contain the expected number of primes for every exponent
strictly above `7/12`, together with the reflected `3/5` interval. -/
def shortIntervalPrimeAsymptotic_claim2326 : Prop :=
  let primeCounting : ℝ → ℝ := fun x =>
    (Nat.primeCounting (Nat.floor x) : ℝ)
  let forward : ℝ → ℝ → ℝ := fun θ x =>
    primeCounting (x + x ^ θ) - primeCounting x
  let expected : ℝ → ℝ → ℝ := fun θ x =>
    x ^ θ / Real.log x
  (∀ θ : ℝ, 7 / 12 < θ →
      (forward θ) ~[atTop] (expected θ)) ∧
    (fun c => primeCounting c - primeCounting (c - c ^ (3 / 5)))
      ~[atTop] (expected (3 / 5))

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
