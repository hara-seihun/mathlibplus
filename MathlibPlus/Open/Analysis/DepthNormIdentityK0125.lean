import Mathlib

namespace MathlibPlus.Open.Analysis.DepthNormIdentityK0125

open scoped BigOperators

noncomputable section

/-- The nonnegative principal real branch of Lambert's W on the inputs used by
this model. -/
def principalLambertW (x : ℝ) : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = x}

/-- The rescaled Lambert function in the admitted coefficient model. -/
def compactLambertW (x : ℝ) : ℝ :=
  principalLambertW (x / (2 * Real.pi))

def compactLambertWNat (j : ℕ) : ℝ :=
  compactLambertW (j : ℝ)

/-- The one-based compact Lambert coefficient. -/
def compactCoefficient (j : ℕ) : ℝ :=
  compactLambertWNat j / (4 * (j : ℝ))

/-- The squared monic-norm product, in the common normalization in which the
zeroth norm is one.  The omitted zeroth factor cancels in every displayed
ratio. -/
def compactNorm (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (2 * k), (compactCoefficient (j + 1)) ^ 2

def compactRowCoefficient (N : ℕ) : ℝ :=
  compactCoefficient N

def trailingLambertAction (m N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc m N, (compactLambertWNat N - compactLambertWNat j)

def macroscopicAction (τ : ℝ) : ℝ :=
  1 - τ + τ * Real.log τ

/-- Claim 8893: the exact compact-model depth norm identity and its
macroscopic action limit. -/
def claim_8893 : Prop :=
  (∀ (n d : ℕ),
      0 < n →
      d ≤ n →
      let N := 2 * n
      let m := 2 * (n - d)
      Real.log
          (compactRowCoefficient N ^ (2 * (N - m)) *
            compactNorm (m / 2) / compactNorm (N / 2)) =
        -2 * trailingLambertAction m N) ∧
    (∀ (d : ℕ → ℕ) (θ : ℝ),
      (∀ k, d k ≤ k) →
      Filter.Tendsto
          (fun k : ℕ => (d k : ℝ) / (k : ℝ))
          Filter.atTop (nhds θ) →
      Filter.Tendsto
          (fun k : ℕ =>
            (1 / (k : ℝ)) *
              Real.log
                (compactRowCoefficient (2 * k) ^ (4 * d k) *
                  compactNorm (k - d k) / compactNorm k))
          Filter.atTop (nhds (-4 * macroscopicAction (1 - θ))))

end

end MathlibPlus.Open.Analysis.DepthNormIdentityK0125
