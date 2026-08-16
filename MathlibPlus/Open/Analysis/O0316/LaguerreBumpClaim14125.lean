import MathlibPlus.Open.Analysis.LaguerreDominance

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0316

open MathlibPlus.Open.Analysis
open Classical

/-- The compact support interval at the leading-monomial threshold. -/
def compactBumpSupport (d : ℕ) : Set ℝ :=
  Set.Icc (generalizedLaguerreTwoThreshold d)
    (generalizedLaguerreTwoThreshold d + 1)

/-- The envelope-saturating bump, with the sign of the degree-`d` leading
monomial on its support and zero outside. -/
noncomputable def envelopeSaturatingBump (c : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  if t ∈ compactBumpSupport d then
    (-1 : ℝ) ^ d * Real.exp (-c * Real.sqrt t)
  else 0

/-- Claim 14125: the compact bump stays inside the exponential envelope and
has the same nonzero sign as `L_d^2` throughout its support. -/
def claim14125 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ d : ℕ, 1 ≤ d →
    (∀ t : ℝ,
      |envelopeSaturatingBump c d t| ≤
        Real.exp (-c * Real.sqrt t)) ∧
      (∀ t : ℝ, t ∈ compactBumpSupport d →
        0 < envelopeSaturatingBump c d t *
          generalizedLaguerreTwo d t)

end MathlibPlus.Open.Analysis.FormalizationBatchO0316
