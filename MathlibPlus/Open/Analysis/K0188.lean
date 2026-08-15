import Mathlib

open scoped Topology

namespace MathlibPlus.Open.Analysis

/--
The reciprocal off-critical factor from admitted claim 10022.  The asymptotic
assertion is expressed at the origin, and the zero/pole assertions use the
numerator and denominator of the displayed complex rational function.
-/
def reciprocalOffCriticalZeroFactor : Prop :=
  ∀ (M d : ℕ) (rho : ℝ) (eta : ℂ),
    M < d →
    0 < rho →
    rho < 1 →
    eta = (rho : ℂ) ^ d →
    let numerator : ℂ → ℂ := fun x =>
      1 + (eta + eta⁻¹) * x ^ d + x ^ (2 * d)
    let denominator : ℂ → ℂ := fun x =>
      1 + x ^ (2 * d)
    let psi : ℂ → ℂ := fun x => numerator x / denominator x
    (∀ x : ℂ, x ≠ 0 → psi x⁻¹ = psi x) ∧
      (fun x : ℂ => psi x - 1) =O[𝓝 (0 : ℂ)] (fun x : ℂ => x ^ d) ∧
      (∀ x : ℂ,
        numerator x = 0 →
          denominator x ≠ 0 ∧
            (‖x‖ = rho ∨ ‖x‖ = rho⁻¹) ∧
            psi x = 0 ∧
            HasDerivAt psi (deriv psi x) x ∧
            deriv psi x ≠ 0) ∧
      (∀ x : ℂ,
        denominator x = 0 → ‖x‖ = 1 ∧ numerator x ≠ 0)

end MathlibPlus.Open.Analysis
