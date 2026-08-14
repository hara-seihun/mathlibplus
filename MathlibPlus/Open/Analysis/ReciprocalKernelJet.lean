import Mathlib

namespace MathlibPlus.Open.Analysis

/--
Claim 7424: the logarithmic first jet of the reciprocal kernel, its time
 derivative, and the second-derivative ratio identity.
-/
def explicitFirstJetAndTimeDerivative : Prop :=
  ∀ (a q t : ℝ),
    let K (u : ℝ) : ℝ :=
      Real.exp (-(a * u) - q * Real.exp (-u)) +
        Real.exp (a * u - q * Real.exp u)
    let z : ℝ := a * t - q * Real.sinh t
    let X : ℝ := deriv (fun u => K u) t / K t
    let X_t : ℝ :=
      deriv (fun u => deriv (fun v => K v) u / K u) t
    let Y : ℝ := deriv (fun u => deriv (fun v => K v) u) t / K t
    X = -q * Real.sinh t +
          (a - q * Real.cosh t) * Real.tanh z ∧
      X_t = -q * Real.cosh t - q * Real.sinh t * Real.tanh z +
          (a - q * Real.cosh t) ^ 2 * (1 / Real.cosh z) ^ 2 ∧
        Y = X ^ 2 + X_t

end MathlibPlus.Open.Analysis
