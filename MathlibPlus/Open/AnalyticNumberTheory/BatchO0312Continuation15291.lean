import Mathlib

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.AnalyticNumberTheory.BatchO0312.Continuation

/-- A finite positive index set carrying the coefficient family. -/
def positiveDivisorSupport (D : Finset ℕ) : Prop :=
  ∀ d ∈ D, 0 < d

/-- The coefficient family vanishes outside its finite displayed support. -/
def finiteCoefficientSupport (D : Finset ℕ) (c : ℕ → ℂ) : Prop :=
  ∀ n, n ∉ D → c n = 0

/-- The literal divisor-convolution coefficient `b_c(n)`. -/
noncomputable def divisorCoefficient
    (D : Finset ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ D.filter (fun d => d ∣ n), c d

/-- The finite partial sums in the natural positive-integer order. -/
noncomputable def orderedCoefficientPartialSum
    (D : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    divisorCoefficient D c (n + 1) *
      Complex.exp (-s * (Real.log ((n + 1 : ℕ) : ℝ) : ℂ))

/-- The finite Dirichlet multiplier appearing in `F_c` away from the zeta pole. -/
noncomputable def dirichletMultiplier
    (D : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ D,
    c d * Complex.exp (-s * (Real.log (d : ℝ) : ℂ))

/-- Claim 15291: the literal divisor-convolution coefficient series converges
in its natural integer order throughout `Re(s)>0` to the pole-removed `F_c`. -/
def claim15291_orderedCoefficientContinuation : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ → ℂ),
    positiveDivisorSupport D →
    finiteCoefficientSupport D c →
    (∑ d ∈ D, c d / (d : ℂ)) = 0 →
    let A : ℂ → ℂ := dirichletMultiplier D c
    ∃ F : ℂ → ℂ,
      ContinuousAt F 1 ∧
      (∀ z : ℂ, z ≠ 1 → F z = A z * riemannZeta z) ∧
      ∀ s : ℂ, 0 < s.re →
        Tendsto
          (fun N : ℕ => orderedCoefficientPartialSum D c s N)
          atTop (𝓝 (F s))

end MathlibPlus.Open.AnalyticNumberTheory.BatchO0312.Continuation
