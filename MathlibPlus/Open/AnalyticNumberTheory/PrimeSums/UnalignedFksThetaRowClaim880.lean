import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/-!
Statement-fidelity registry node for admitted claim 880.  The node records
both the corrected first FKS theta-row exponent and the exact
Proposition-17 evaluation used by the accepted C-0058 certificate.
-/

/--
Claim 880: the first two FKS Table 2 theta rows print `1.9537 · 10⁻⁹`, but
Proposition 17 at `x₀ = 10^19` gives a value in the corrected
`1.953644... · 10⁻⁸` interval; `1.9537 · 10⁻⁸` is the valid outward decimal.
-/
def correctedFirstFksThetaRow_claim880 : Prop :=
  let x₀ : ℝ := 10 ^ 19
  let epsilon₀ : ℝ :=
    1.9220e-8 +
      1.00000002 *
        (Real.rpow x₀ (-1 / 2 : ℝ) +
          Real.rpow x₀ (-2 / 3 : ℝ) +
          Real.rpow x₀ (-4 / 5 : ℝ)) +
      0.94 *
        (Real.rpow x₀ (-3 / 4 : ℝ) +
          Real.rpow x₀ (-5 / 6 : ℝ) +
          Real.rpow x₀ (-9 / 10 : ℝ))
  1.9537e-9 < epsilon₀ ∧
    1.95364e-8 < epsilon₀ ∧
    epsilon₀ < 1.95365e-8 ∧
    epsilon₀ < 1.9537e-8

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
