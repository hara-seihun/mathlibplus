import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim18889

noncomputable def temperedLocalFactor (p B : ℝ) (q : ℂ) : ℂ :=
  Complex.exp (q * (Real.log p : ℂ)) + (B : ℂ) +
    Complex.exp (-q * (Real.log p : ℂ))

noncomputable def finiteTemperedProduct
    {ι : Type*} [Fintype ι]
    (J : Finset ι) (p B : ι → ℝ) (q : ℂ) : ℂ :=
  ∏ i ∈ J, temperedLocalFactor (p i) (B i) q

/-- Claim 18889: a finite product of the explicit tempered local factors is
an exponential polynomial, and its logarithmic size is at most linear along
the positive real ray after its real zeros are excluded. -/
def finiteTemperedProductsHaveExponentialPolynomialGrowth_claim18889 : Prop :=
  ∀ {ι : Type*} [Fintype ι]
    (J : Finset ι) (p B : ι → ℝ),
    (∀ i : ι, i ∈ J → 1 < p i ∧ |B i| ≤ 2) →
      let P : ℂ → ℂ := finiteTemperedProduct J p B
      (∃ m : ℕ, ∃ rate : Fin m → ℂ, ∃ coeff : Fin m → Polynomial ℂ,
        ∀ q : ℝ,
          P (q : ℂ) =
            ∑ k : Fin m,
              Polynomial.eval (q : ℂ) (coeff k) *
                Complex.exp (rate k * (q : ℂ))) ∧
      (∀ᶠ q : ℝ in Filter.atTop, P (q : ℂ) ≠ 0) ∧
      (fun q : ℝ => Real.log ‖P (q : ℂ)‖) =O[Filter.atTop]
        (fun q : ℝ => q)

end MathlibPlus.Open.Analysis.Claim18889
