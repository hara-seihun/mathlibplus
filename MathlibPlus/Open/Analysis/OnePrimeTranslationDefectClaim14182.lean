import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- Claim 14182: for a centered zero coordinate and a prime, the one-prime
translation defect is the exact radial defect, and approximate eigenvalues are
exactly on the centered critical axis. -/
def onePrimeTranslationDefect_claim14182 : Prop :=
  ∀ (ρ : ℂ) (p : ℕ), Nat.Prime p →
    let lam : ℂ := ρ - (1 / 2 : ℂ)
    let beta : ℝ := lam.re
    let a : ℝ := Real.log (p : ℝ)
    let z : ℂ := Complex.exp ((a : ℂ) * lam)
    ∀ (τ :
        Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
          Lp ℂ 2 (volume : Measure ℝ)),
      (∀ f : Lp ℂ 2 (volume : Measure ℝ),
        (τ f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + a)) →
      (sInf
          {d : ℝ |
            ∃ f : Lp ℂ 2 (volume : Measure ℝ),
              ‖f‖ = 1 ∧ d = ‖τ f - z • f‖} =
          |Real.rpow (p : ℝ) beta - 1|) ∧
        ((∀ ε : ℝ, 0 < ε →
            ∃ f : Lp ℂ 2 (volume : Measure ℝ),
              ‖f‖ = 1 ∧ ‖τ f - z • f‖ < ε) ↔
          beta = 0)

end MathlibPlus.Open.Analysis
