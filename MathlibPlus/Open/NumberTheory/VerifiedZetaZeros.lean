import Mathlib

/-!
# Verified critical-line location through T₁

This registry node formalizes admitted claim 272. For an analytic function, a zero
has multiplicity one exactly when its first derivative there is nonzero, so the
claim's simplicity conclusion is stated as `deriv riemannZeta ρ ≠ 0`.
-/

namespace MathlibPlus.Open.NumberTheory

/-- Every nontrivial Riemann-zeta zero in the positive-imaginary half-plane through
height `3000175332801` lies on the critical line and is simple. -/
def verifiedCriticalLineThroughT1 : Prop :=
  ∀ ρ : ℂ,
    riemannZeta ρ = 0 →
    0 < ρ.im →
    ρ.im ≤ 3000175332801 →
    ρ.re = (1 : ℝ) / 2 ∧ deriv riemannZeta ρ ≠ 0

end MathlibPlus.Open.NumberTheory
