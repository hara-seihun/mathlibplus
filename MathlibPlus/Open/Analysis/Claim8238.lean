import Mathlib

namespace MathlibPlus.Open.Analysis.Claim8238

noncomputable section

/-- The defect in the logarithmic-jet form, with the source's first and
second derivatives represented by `deriv` and `deriv (deriv ·)`. -/
def logarithmicJetDefect (G : ℝ → ℝ) (a : ℝ) : ℝ :=
  a ^ 2 * (deriv G a) ^ 2 -
    a * G a * deriv G a -
    a ^ 2 * G a * deriv (deriv G) a

/-- Exact logarithmic-jet form of the radial tangent defect. -/
def logarithmicJetDefectIdentity : Prop :=
  ∀ (G : ℝ → ℝ) (a : ℝ),
    0 < G a →
    ContDiffAt ℝ 2 G a →
    let h : ℝ → ℝ := fun x => Real.log (G x)
    logarithmicJetDefect G a =
        -a * (G a) ^ 2 * deriv (fun x => x * deriv h x) a ∧
      logarithmicJetDefect G a / (G a) ^ 2 =
        -a * (deriv h a + a * deriv (deriv h) a)

end

end MathlibPlus.Open.Analysis.Claim8238
