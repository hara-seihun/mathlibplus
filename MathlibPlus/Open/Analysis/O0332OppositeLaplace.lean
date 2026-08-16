import Mathlib
import MathlibPlus.Analysis.AllPassCayleyRelocation

open MathlibPlus.Analysis.O0332

namespace MathlibPlus.Open.Analysis.O0332

noncomputable section

/-- Evaluation of the real interpolating polynomial at a complex point. -/
noncomputable def realPolynomialValue (P : Polynomial ℝ) (u : ℂ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℝ ℂ) u P

/-- The residue of the all-pass product at a pole, represented by its
meromorphic trailing coefficient. -/
noncomputable def allPassResidue (a gamma : ℝ) (p : ℂ) : ℂ :=
  meromorphicTrailingCoeffAt (allPassProduct a gamma) p

/-- The exact simple-pole and residue interface used for the Laplace pair. -/
def simplePoleWithResidueMinusOne (F : ℂ → ℂ) (p : ℂ) : Prop :=
  MeromorphicAt F p ∧
    meromorphicOrderAt F p = (-1 : ℤ) ∧
    meromorphicTrailingCoeffAt F p = (-1 : ℂ)

/-- Claim 14213: the delayed all-pass interpolation pair has identical
imaginary-axis modulus but opposite half-plane pole structure. -/
def claim14213OppositeLaplaceAnalyticStructure : Prop :=
  ∀ (a gamma : ℝ) (K : ℕ) (L T : ℝ) (N : ℕ),
    0 < a ∧
      a < 1 / 2 ∧
      0 < gamma ∧
      1 < L ∧
      K + 6 ≤ N →
      ∃ P : Polynomial ℝ,
        let quartet (p : ℂ) : Prop :=
          p = -(a : ℂ) + (gamma : ℂ) * Complex.I ∨
            p = -(a : ℂ) - (gamma : ℂ) * Complex.I ∨
            p = -((1 - a : ℝ) : ℂ) + (gamma : ℂ) * Complex.I ∨
            p = -((1 - a : ℝ) : ℂ) - (gamma : ℂ) * Complex.I
        let interpolation : Prop :=
          P.degree ≤ 3 ∧
            (∀ p : ℂ, quartet p →
              allPassResidue a gamma p ≠ 0 ∧
                realPolynomialValue P p =
                  -((p + (L : ℂ)) ^ N) * Complex.exp ((T : ℂ) * p) /
                    allPassResidue a gamma p) ∧
            (∀ Q : Polynomial ℝ,
              Q.degree ≤ 3 →
                (∀ p : ℂ, quartet p →
                  allPassResidue a gamma p ≠ 0 ∧
                    realPolynomialValue Q p =
                      -((p + (L : ℂ)) ^ N) * Complex.exp ((T : ℂ) * p) /
                        allPassResidue a gamma p) →
                Q = P)
        let F₀ : ℂ → ℂ := fun u =>
          Complex.exp (-((T : ℂ) * u)) *
            realPolynomialValue P u /
              (u + (L : ℂ)) ^ N
        let F₁ : ℂ → ℂ := fun u => allPassProduct a gamma u * F₀ u
        interpolation ∧
          AnalyticOnNhd ℂ F₀ {u : ℂ | (-1 / 2 : ℝ) < u.re} ∧
          (∀ p : ℂ, quartet p →
            simplePoleWithResidueMinusOne F₁ p) ∧
          (∀ τ : ℝ,
            Complex.normSq (F₁ ((τ : ℂ) * Complex.I)) =
              Complex.normSq (F₀ ((τ : ℂ) * Complex.I))) ∧
          (-1 / 2 : ℝ) < (-(a : ℂ)).re ∧
          (-(a : ℂ)).re < 0 ∧
          (-(1 - a : ℂ)).re < (-1 / 2 : ℝ)

end

end MathlibPlus.Open.Analysis.O0332
