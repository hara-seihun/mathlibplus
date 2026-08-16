import Mathlib
import MathlibPlus.Open.Analysis.O0317Claims14137And14148

namespace MathlibPlus.Open.ResearchFormalization.O0317

open scoped BigOperators
open Filter
open MathlibPlus.Open.Analysis.O0317

noncomputable section

/-- The finite Gamma quotient appearing before removable singularities are
filled by analytic continuation. -/
noncomputable def rawGammaPochhammerQuotient (k : ℕ) (z : ℂ) : ℂ :=
  Complex.Gamma ((k : ℂ) + 1 - z) /
    (Complex.Gamma (1 - z) * Complex.Gamma ((k : ℂ) + 1))

/-- The regular points at which the totalized Gamma quotient is the literal
meromorphic quotient rather than a cancelled value at a pole. -/
def gammaPochhammerRegular (k : ℕ) (z : ℂ) : Prop :=
  Complex.Gamma (1 - z) ≠ 0 ∧
    Complex.Gamma ((k : ℂ) + 1 - z) ≠ 0

/-- The finite-product/Gamma identity with its cancellation semantics: the
finite product is the entire continuation of the raw quotient from its regular
set. -/
def gammaPochhammerContinuation (k : ℕ) : Prop :=
  ∃ G : ℂ → ℂ,
    Differentiable ℂ G ∧
      (∀ z : ℂ, G z = newtonPochhammer k z) ∧
      (∀ z : ℂ, gammaPochhammerRegular k z →
        G z = rawGammaPochhammerQuotient k z)

/-- The finite partial sums of the reciprocal-zeta Newton series. -/
noncomputable def reciprocalZetaNewtonPartial (m : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m,
    (baezDuarteCoefficient k) * newtonPochhammer k (s / 2)

/-- Claim 14133: the Pochhammer/Gamma identity is understood by analytic
continuation at cancelled Gamma poles, and the reciprocal-zeta Newton series
converges locally uniformly on `Re(s) > 1`. -/
def claim14133 : Prop :=
  (∀ k : ℕ, gammaPochhammerContinuation k) ∧
    (∀ s : ℂ, 1 < s.re →
      (riemannZeta s)⁻¹ =
        ∑' k : ℕ,
          baezDuarteCoefficient k * newtonPochhammer k (s / 2)) ∧
    (∀ K : Set ℂ, IsCompact K →
      (∀ s : ℂ, s ∈ K → 1 < s.re) →
        TendstoUniformlyOn reciprocalZetaNewtonPartial
          (fun s : ℂ => (riemannZeta s)⁻¹)
          Filter.atTop K)

end

end MathlibPlus.Open.ResearchFormalization.O0317
