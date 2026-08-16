import MathlibPlus.Analysis.Claim13408
import MathlibPlus.Open.Analysis.Claim13420

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ExplicitSecondCumulant13428

noncomputable section

open MathlibPlus.Open.Analysis.Claim13420

/-- The finite renormalized Euler product `B_y=A_y exp(P_y)`, using the
reviewed finite Euler product and prime-sum carriers. -/
def renormalizedFiniteEulerProduct (y : ℕ) (z : ℂ) : ℂ :=
  MathlibPlus.Analysis.Claim13408.finiteEulerProduct y z *
    Complex.exp (primeSum y z)

/-- The analytic logarithm branch of `B_y` supplied by the finite cumulant
sum, rather than the principal logarithm of a product. -/
def renormalizedFiniteLogBranch (y : ℕ) (z : ℂ) : ℂ :=
  ∑ p ∈ primeCutoff y,
    (Complex.log (1 - primePower p z) + primePower p z)

/-- The limiting second-cumulant logarithm branch over all primes. -/
def renormalizedLimitLogBranch (z : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    (Complex.log (1 - primePower p z) + primePower p z)

/-- The corresponding nonvanishing-limit carrier. -/
def renormalizedLimit (z : ℂ) : ℂ :=
  Complex.exp (renormalizedLimitLogBranch z)

/-- Explicit tail bound for the analytic logarithm branches on the indicated
half-plane. -/
def explicitSecondCumulantTailBound : Prop :=
  ∀ (σ₀ : ℝ) (z : ℂ) (y : ℕ),
    (1 / 2 : ℝ) < σ₀ →
    σ₀ ≤ z.re →
    1 < y →
      ‖renormalizedLimitLogBranch z -
          renormalizedFiniteLogBranch y z‖ ≤
        Real.rpow (y : ℝ) (1 - 2 * σ₀) /
          ((2 * σ₀ - 1) *
            (1 - Real.rpow (y : ℝ) (-σ₀)))

end

end MathlibPlus.Open.Analysis.ExplicitSecondCumulant13428
