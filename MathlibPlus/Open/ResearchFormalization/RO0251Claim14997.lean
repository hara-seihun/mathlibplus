import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RO0251Claim14997

/-- Claim 14997: the sharp exterior Chebyshev lower bound and the displayed
real/complex extremizers, with the coefficient fields and interval supremum
kept explicit. -/
def chebyshevExteriorExtremal_claim14997 : Prop :=
  (∀ (d : ℕ) (P : Polynomial ℝ) (a b : ℝ),
    P.natDegree ≤ d →
    P.eval (0 : ℝ) = 1 →
    0 < a →
    a < b →
    let T : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (d : ℤ)
    let denominator : ℝ := T.eval (-(a + b) / (b - a))
    let interval : Set ℝ := Set.Icc a b
    let supNorm (Q : Polynomial ℝ) : ℝ :=
      sSup ((fun u : ℝ => |Q.eval u|) '' interval)
    let Pstar : Polynomial ℝ :=
      (denominator⁻¹) •
        T.comp (((b - a)⁻¹ : ℝ) •
          ((2 : ℝ) • Polynomial.X - Polynomial.C (a + b)))
    1 / |denominator| ≤ supNorm P ∧
      Pstar.eval 0 = 1 ∧
      supNorm Pstar = 1 / |denominator|) ∧
  (∀ (d : ℕ) (P : Polynomial ℂ) (a b : ℝ),
    P.natDegree ≤ d →
    P.eval (0 : ℂ) = 1 →
    0 < a →
    a < b →
    let T : Polynomial ℂ := Polynomial.Chebyshev.T ℂ (d : ℤ)
    let denominator : ℂ := T.eval (((-(a + b) / (b - a) : ℝ) : ℂ))
    let interval : Set ℝ := Set.Icc a b
    let supNorm (Q : Polynomial ℂ) : ℝ :=
      sSup ((fun u : ℝ => ‖Q.eval (u : ℂ)‖) '' interval)
    let Pstar : Polynomial ℂ :=
      (denominator⁻¹) •
        T.comp (((b - a : ℝ)⁻¹ : ℂ) •
          ((2 : ℂ) • Polynomial.X - Polynomial.C ((a + b : ℝ) : ℂ)))
    1 / ‖denominator‖ ≤ supNorm P ∧
      Pstar.eval (0 : ℂ) = 1 ∧
      supNorm Pstar = 1 / ‖denominator‖)

end MathlibPlus.Open.ResearchFormalization.RO0251Claim14997
