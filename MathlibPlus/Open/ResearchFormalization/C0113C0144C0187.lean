import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0113C0144C0187

noncomputable section
open Classical

/-- Claim 1763.  The integer generator is an explicit input constrained by the
source norm.  The cosine coefficients are existentially retained, but are tied
pointwise to the displayed Fejer--Riesz polynomial rather than left as an
unrelated callback. -/
def exactFejerRieszPolynomial_claim1763 (b : Fin 17 → ℤ) : Prop :=
  (∑ j : Fin 17, ((b j : ℝ) ^ 2)) = 14912370 ∧
    ∃ a : Fin 17 → ℝ,
      (∀ x : ℝ,
        (14912370 : ℝ)⁻¹ *
            ‖∑ j : Fin 17,
                (b j : ℂ) * Complex.exp (Complex.I * (j.1 : ℂ) * (x : ℂ))‖ ^ 2 =
          ∑ k : Fin 17, a k * Real.cos ((k.1 : ℝ) * x)) ∧
        ∀ x : ℝ,
          0 ≤ (14912370 : ℝ)⁻¹ *
            ‖∑ j : Fin 17,
                (b j : ℂ) * Complex.exp (Complex.I * (j.1 : ℂ) * (x : ℂ))‖ ^ 2

private noncomputable def zetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  if h : ∃ n : ℕ, iteratedDeriv n riemannZeta ρ ≠ 0 then Nat.find h else 0

private noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  Nat.card {p : ℂ × ℕ //
    riemannZeta p.1 = 0 ∧
      0 < p.1.re ∧ p.1.re < 1 ∧
      0 < p.1.im ∧ p.1.im ≤ T ∧
      p.2 < zetaZeroMultiplicity p.1}

/-- Claim 2274.  `N(T)` is fixed to the standard positive-imaginary,
nontrivial-zero count with analytic multiplicity; it is not an arbitrary
function parameter. -/
def finiteHeightCriticalLineVerification_claim2274 : Prop :=
  (∀ ρ : ℂ,
    riemannZeta ρ = 0 →
      0 < ρ.re → ρ.re < 1 →
      0 < ρ.im → ρ.im ≤ 3000175332800 →
      ρ.re = (1 : ℝ) / 2) ∧
    zetaZeroCount 3000175332800 = 12363153437138

/-- Claim 2774.  First jets are represented by two complex coordinates, so a
complex-bilinear alternating scalar concomitant is classified by the
Wronskian.  The exact gauged quadratic pencil, the parity/conjugation partner
condition, the vanishing odd jet at an even symmetry point, and the explicit
positive even two-Gaussian off-axis-zero model are all retained. -/
def scalarFirstJetAppellObstruction_claim2774 : Prop :=
  (∀ (a H0 : ℂ) (T : ℂ → ℂ),
    (∀ lam : ℂ, T lam = lam ^ 2 - 2 * a * lam + 4 * H0) →
      ∀ (B : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] ℂ),
        (∀ u : Fin 2 → ℂ, B u u = 0) →
          ∃ c : ℂ, ∀ u v : Fin 2 → ℂ,
            B u v = c * (u 0 * v 1 - u 1 * v 0)) ∧
    (∀ lam : ℂ,
      (-lam = starRingEnd ℂ lam ↔ lam + starRingEnd ℂ lam = 0) ∧
        (lam + starRingEnd ℂ lam = 0 ↔ lam.re = 0)) ∧
    (∀ f : ℝ → ℂ, ∀ d : ℝ →L[ℝ] ℂ,
      (∀ x : ℝ, f (-x) = f x) → HasFDerivAt f d 0 → d = 0) ∧
    (∃ c₁ c₂ a₁ a₂ : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧ 0 < a₁ ∧ 0 < a₂ ∧ a₁ ≠ a₂ ∧
        let F : ℂ → ℂ := fun z =>
          (c₁ : ℂ) * Complex.exp (-(a₁ : ℂ) * z ^ 2) +
            (c₂ : ℂ) * Complex.exp (-(a₂ : ℂ) * z ^ 2)
        (∀ x : ℝ,
            0 < c₁ * Real.exp (-a₁ * x ^ 2) +
              c₂ * Real.exp (-a₂ * x ^ 2)) ∧
          (∀ x : ℝ, F (x : ℂ) = F (-(x : ℂ))) ∧
          HasFDerivAt (fun x : ℝ => F (x : ℂ))
            (0 : ℝ →L[ℝ] ℂ) 0 ∧
          ∃ z : ℂ, z.im ≠ 0 ∧ F z = 0)

end
end MathlibPlus.Open.ResearchFormalization.C0113C0144C0187
