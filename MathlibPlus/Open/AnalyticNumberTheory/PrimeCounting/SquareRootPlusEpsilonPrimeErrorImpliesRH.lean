import Mathlib

open Asymptotics Filter

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/--
Claim 17420: a square-root-plus-epsilon Chebyshev-psi error bound for every
positive epsilon implies the Riemann hypothesis.  The `O_ε` notation is
represented by `IsBigO atTop`, and the real power is `Real.rpow`.
-/
def squareRootPlusEpsilonPrimeErrorImpliesRH_claim17420 : Prop :=
  (∀ ε : ℝ, 0 < ε →
    IsBigO atTop
      (fun x : ℝ => Chebyshev.psi x - x)
      (fun x : ℝ => Real.rpow x (1 / 2 + ε))) →
    RiemannHypothesis

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
