import MathlibPlus.Open.Combinatorics.Claim7519

open scoped BigOperators Interval

namespace MathlibPlus.Open.Analysis.Claim7523

noncomputable section

open MathlibPlus.Open.Combinatorics.Claim7519

/-- The real zeta normalizing factor on the half-plane used by the Gibbs law. -/
noncomputable def zetaReal7523 (σ : ℝ) : ℝ :=
  (riemannZeta (σ : ℂ)).re

/-- The Gibbs mass of an Euler Scarweave at real parameter `σ`. -/
noncomputable def gibbsMass7523 (σ : ℝ) (X : EulerScarweave) : ℝ :=
  scarweaveWeight X * Real.rpow (seamInteger X : ℝ) (-σ) / zetaReal7523 σ

/-- The seam height observable. -/
noncomputable def seamHeight7523 (X : EulerScarweave) : ℝ :=
  Real.log (seamInteger X : ℝ)

/-- The Gibbs expectation of seam height. -/
noncomputable def meanSeamHeight7523 (σ : ℝ) : ℝ :=
  ∑' X : EulerScarweave, seamHeight7523 X * gibbsMass7523 σ X

/-- The Gibbs variance of seam height. -/
noncomputable def seamHeightVariance7523 (σ : ℝ) : ℝ :=
  ∑' X : EulerScarweave,
    (seamHeight7523 X - meanSeamHeight7523 σ) ^ 2 * gibbsMass7523 σ X

/-- The negative prime Loewner channel for the Scarweave Gibbs law. -/
def claim7523_negativePrimeLoewnerChannel : Prop :=
  ∀ (lam mu : ℝ),
    lam ≠ mu →
    1 / 2 < lam →
    1 / 2 < mu →
    let A : ℝ → ℝ := fun t => meanSeamHeight7523 (1 / 2 + t)
    let V : ℝ → ℝ := fun t => seamHeightVariance7523 (1 / 2 + t)
    let G : ℝ → ℝ := fun t => A t / t
    let r : ℝ := min lam mu
    let R : ℝ := max lam mu
    let Vbar : ℝ := (R - r)⁻¹ * (∫ t in r..R, V t)
    (G lam - G mu) / (lam ^ 2 - mu ^ 2) =
        -(A r + r * Vbar) / (r * R * (r + R)) ∧
      -(A r + r * Vbar) / (r * R * (r + R)) < 0

end

end MathlibPlus.Open.Analysis.Claim7523
