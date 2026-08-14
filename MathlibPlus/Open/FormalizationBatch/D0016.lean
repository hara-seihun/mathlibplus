import Mathlib

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.D0016

def radialD (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * deriv f r

def radialQ (x : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  radialD (radialD f) r + x ^ 2 * f r

def radialL (x : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  r⁻¹ * radialQ x (fun y => y * radialQ x f y) r

/-- Claim 4486: the two radial shell operators. -/
def radial_operators_claim : Prop :=
  (∀ (x : ℝ) (f : ℝ → ℝ) (r : ℝ),
    radialQ x f r = (r * deriv (fun y => y * deriv f y) r) + x ^ 2 * f r) ∧
    (∀ (x : ℝ) (f : ℝ → ℝ) (r : ℝ),
      radialL x f r = r⁻¹ * radialQ x (fun y => y * radialQ x f y) r)

end MathlibPlus.Open.FormalizationBatch.D0016
