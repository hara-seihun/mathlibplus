import Mathlib

namespace MathlibPlus.Open.Analysis.HedenmalmBatch

/-- The logarithmic-coordinate differential expressions from Claim 9516. -/
noncomputable def logarithmicD (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -Complex.I * deriv f x

noncomputable def logarithmicL (φ : ℝ → ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -Complex.I * (deriv f x + Complex.ofReal (deriv φ x) * f x)

noncomputable def kernelProfile (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun x => Real.exp (-φ x)

/--
Claim 9516: in logarithmic coordinates the pair is
`D = -i ∂ₓ` and `L = -i (∂ₓ + φ')`, with positive profile `h = exp (-φ)`.
-/
def claim9516_logarithmic_normal_form : Prop :=
  ∀ (φ : ℝ → ℝ) (f : ℝ → ℂ),
    logarithmicD f = (fun x => -Complex.I * deriv f x) ∧
      logarithmicL φ f =
        (fun x => -Complex.I * (deriv f x + Complex.ofReal (deriv φ x) * f x)) ∧
      kernelProfile φ = (fun x => Real.exp (-φ x)) ∧
      ∀ x, 0 < kernelProfile φ x

end MathlibPlus.Open.Analysis.HedenmalmBatch
