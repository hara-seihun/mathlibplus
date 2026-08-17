import Mathlib

namespace MathlibPlus.Open.Analysis.Claim18827

open scoped BigOperators

private noncomputable def gaussianTwoPointTransform {ι : Type*}
    (J : Finset ι) (C a b : ℝ) (c : ι → ℝ) (z : ℂ) : ℂ :=
  (C : ℂ) * Complex.exp ((a : ℂ) * z ^ 2 + (b : ℂ) * z) *
    J.prod (fun j => Complex.cosh ((c j : ℂ) * z))

/-- Claim 18827: the finite Gaussian/two-point product class satisfies
condition (I) at every positive real abscissa and every valid complex point.
The quotient is asserted only when its complex denominator is nonzero. -/
def gaussianTwoPointProductConditionI_claim18827 : Prop :=
  ∀ {ι : Type*}
    (J : Finset ι) (C a b : ℝ) (c : ι → ℝ),
    0 < C → 0 ≤ a →
      let F := gaussianTwoPointTransform J C a b c
      ∀ x : ℝ, 0 < x → ∀ t : ℝ,
        F ((x : ℂ) + (t : ℂ) * Complex.I) ≠ 0 →
          Complex.re
              (deriv F ((x : ℂ) + (t : ℂ) * Complex.I) /
                F ((x : ℂ) + (t : ℂ) * Complex.I)) ≥
            Complex.re (deriv F (x : ℂ) / F (x : ℂ))

end MathlibPlus.Open.Analysis.Claim18827
