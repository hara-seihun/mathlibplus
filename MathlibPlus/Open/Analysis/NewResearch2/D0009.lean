import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.NewResearch2.D0009

noncomputable section

private def finiteOrderEntire (X : ℂ → ℂ) : Prop :=
  Differentiable ℂ X ∧
    ∃ ρ C R : ℝ, 0 ≤ ρ ∧ 0 ≤ C ∧ 0 < R ∧
      ∀ z : ℂ, R ≤ ‖z‖ →
        ‖X z‖ ≤ Real.exp (C * Real.rpow ‖z‖ ρ)

private def complexPiPow (s : ℂ) : ℂ :=
  Complex.exp ((-s / 2) * Complex.log (Real.pi : ℂ))

private def completedCarrierNormalization (X : ℂ → ℂ) (s : ℂ) : ℂ :=
  2 * X (-Complex.I * (s - (1 / 2 : ℂ))) /
    (s * (s - 1) * complexPiPow s * Complex.Gamma (s / 2))

/-- Claim 4389: completed-carrier normalization before logarithmic differentiation. -/
def completedCarrierNormalization_claim4389 : Prop :=
  ∀ X : ℂ → ℂ,
    (∀ z : ℂ, X (-z) = X z) → finiteOrderEntire X →
      ∀ s : ℂ,
        completedCarrierNormalization X s =
          2 * X (-Complex.I * (s - (1 / 2 : ℂ))) /
            (s * (s - 1) *
              Complex.exp ((-s / 2) * Complex.log (Real.pi : ℂ)) *
              Complex.Gamma (s / 2))

private def localXi (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

private def riemannXiEven (z : ℂ) : ℂ :=
  localXi ((1 / 2 : ℂ) + Complex.I * z)

/-- Claim 4391: the normalized Riemann Xi carrier specializes to zeta. -/
def xiSpecializesToZeta_claim4391 : Prop :=
  ∀ s : ℂ,
    completedCarrierNormalization riemannXiEven s = riemannZeta s

private def vonMangoldtWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

private def complexDirichletTerm (n : ℕ) (s : ℂ) : ℂ :=
  if 2 ≤ n then
    (vonMangoldtWeight n : ℂ) * Complex.exp (-s * Complex.log (n : ℂ))
  else 0

private def xiArithmeticLog (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- Claim 4392: the Xi arithmetic logarithm and the von Mangoldt series. -/
def xiArithmeticLogVonMangoldt_claim4392 : Prop :=
  ∀ s : ℂ, 1 < s.re →
    xiArithmeticLog s = ∑' n : ℕ, complexDirichletTerm n s ∧
      Summable (fun n : ℕ => ‖complexDirichletTerm n s‖) ∧
      (∀ n : ℕ, 2 ≤ n →
        complexDirichletTerm n s =
          (vonMangoldtWeight n : ℂ) * Complex.exp (-s * Complex.log (n : ℂ)))

private def completedArithmeticLog (X : ℂ → ℂ) (s : ℂ) : ℂ :=
  -deriv (completedCarrierNormalization X) s /
    completedCarrierNormalization X s

private def canonicalDefect (X : ℂ → ℂ) (s : ℂ) : ℂ :=
  completedArithmeticLog X s - xiArithmeticLog s

/-- Claim 4394: the canonical completed-carrier defect. -/
def canonicalDefect_claim4394 : Prop :=
  ∀ X : ℂ → ℂ, ∀ s : ℂ,
    canonicalDefect X s = completedArithmeticLog X s - xiArithmeticLog s ∧
      (canonicalDefect X s = 0 ↔
        completedArithmeticLog X s = xiArithmeticLog s)

end
end MathlibPlus.Open.Analysis.NewResearch2.D0009
