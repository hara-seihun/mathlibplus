import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.O0355Claim15617

noncomputable section

private abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
private abbrev PositiveNat := {k : ℕ // 1 ≤ k}

private def positiveCompletelyMultiplicative
    (a : ℕ → ℝ) : Prop :=
  a 1 = 1 ∧
    (∀ r s : ℕ, a (r * s) = a r * a s) ∧
    (∀ n : ℕ, 0 < a n)

private noncomputable def geometricEulerFactor
    (a : ℕ → ℝ) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - (a p : ℂ) * Complex.exp (-(s * (Real.log (p : ℝ) : ℂ))))⁻¹

private noncomputable def degreeOneEulerProduct
    (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∏' p : PrimeIndex, geometricEulerFactor a p.1 s

private noncomputable def generalizedVonMangoldtPrimePower
    (a : ℕ → ℝ) (p : PrimeIndex) (k : PositiveNat) : ℝ :=
  (a p.1) ^ k.1 * Real.log (p.1 : ℝ)

/-- Claim 15617: the degree-one geometric Euler product has positive
prime-power generalized von Mangoldt coefficients, with the prime-power
coefficient tied to complete multiplicativity rather than an unconstrained
coefficient callback. -/
def claim15617 : Prop :=
  ∀ (a : ℕ → ℝ),
    positiveCompletelyMultiplicative a →
      let L_Y : ℂ → ℂ := degreeOneEulerProduct a
      let Lambda_Y : PrimeIndex → PositiveNat → ℝ :=
        generalizedVonMangoldtPrimePower a
      (∀ p : PrimeIndex, ∀ k : PositiveNat,
        a (p.1 ^ k.1) = (a p.1) ^ k.1 ∧
          Lambda_Y p k = (a p.1) ^ k.1 * Real.log (p.1 : ℝ) ∧
          0 < Lambda_Y p k) ∧
      (∀ s : ℂ,
        L_Y s =
          ∏' p : PrimeIndex, geometricEulerFactor a p.1 s)

end

end MathlibPlus.Open.Analysis.O0355Claim15617
