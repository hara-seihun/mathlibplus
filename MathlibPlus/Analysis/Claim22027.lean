import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim22027

open scoped ComplexConjugate

/-- The pointwise quadratic polarization of the first-Laguerre discriminant.
The three complex arguments represent `E`, `E'`, and `E''` at one point;
conjugate differentiation is therefore already reflected in the two jet sums. -/
theorem firstLaguerreDiscriminantPolarization (e e₁ e₂ : ℂ) :
    Complex.re ((e₁ + conj e₁) ^ 2 - (e + conj e) *
        (e₂ + conj e₂)) =
      2 * (Complex.normSq e₁ - (e * conj e₂).re +
        ((e₁ ^ 2 - e * e₂).re)) := by
  rw [Complex.add_conj e₁, Complex.add_conj e, Complex.add_conj e₂]
  simp [pow_two, Complex.normSq_apply, Complex.mul_re]
  ring

end MathlibPlus.Analysis.Claim22027
