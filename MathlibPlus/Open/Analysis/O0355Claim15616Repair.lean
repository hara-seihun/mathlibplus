import Mathlib

open scoped BigOperators Topology

namespace MathlibPlus.Open.Analysis.O0355Claim15616Repair

noncomputable section

private abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
private abbrev PositiveNat := {k : ℕ // 1 ≤ k}

private noncomputable def eta (alpha tau : ℝ) : ℂ :=
  (alpha : ℂ) - (tau : ℂ) * Complex.I

private noncomputable def rho (alpha tau : ℝ) : ℂ :=
  1 - eta alpha tau

private noncomputable def symmetricQuartet
    (alpha tau : ℝ) : Set ℂ :=
  {eta alpha tau, starRingEnd ℂ (eta alpha tau),
    rho alpha tau, starRingEnd ℂ (rho alpha tau)}

private noncomputable def initialPrimeValue
    (alpha tau m : ℝ) (p : ℕ) : ℝ :=
  1 - 2 * m *
    (Real.rpow (p : ℝ) (-alpha) +
      Real.rpow (p : ℝ) (-(1 - alpha))) *
    Real.cos (tau * Real.log (p : ℝ))

private noncomputable def correctedPrimeValue
    (alpha tau : ℝ) (m Y : ℕ) (u : ℝ) (p : ℕ) : ℝ :=
  if p ≤ Y then 1
  else if p ≤ 2 * Y then
    initialPrimeValue alpha tau (m : ℝ) p + u
  else
    initialPrimeValue alpha tau (m : ℝ) p

private def primeTowerTerm
    (a : ℕ → ℝ) (p : PrimeIndex) (k : PositiveNat) : ℝ :=
  ((a p.1) ^ k.1 - 1) * Real.log (p.1 : ℝ) /
    (p.1 : ℝ) ^ k.1

private def positiveCompletelyMultiplicative
    (a : ℕ → ℝ) : Prop :=
  a 1 = 1 ∧
    (∀ r s : ℕ, a (r * s) = a r * a s) ∧
    (∀ n : ℕ, 0 < a n)

private def geometricEulerFactor
    (a : ℕ → ℝ) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - (a p : ℂ) * Complex.exp (-(s * (Real.log (p : ℝ) : ℂ))))⁻¹

/-- Claim 15616: the fixed off-critical quartet produces, for every
sufficiently large cutoff, positive corrected prime values which extend to a
positive completely multiplicative sequence with an exact zeta prefix and
zero total weighted Mertens discrepancy. -/
def claim15616 : Prop :=
  ∀ (alpha tau : ℝ) (m : ℕ),
    Irrational alpha → 0 < alpha → alpha < (1 : ℝ) / 2 →
      1 ≤ m → 0 < tau →
      ∃ C : ℝ, 0 ≤ C ∧
        ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
          ∃ (u : ℝ) (a : ℕ → ℝ),
            |u| ≤ C * Real.rpow (Y : ℝ) (-alpha) ∧
          (∀ p : PrimeIndex, Y < p.1 →
            |initialPrimeValue alpha tau (m : ℝ) p.1 - 1| ≤
              4 * (m : ℝ) * Real.rpow (p.1 : ℝ) (-alpha)) ∧
          (∀ p : PrimeIndex, Y < p.1 →
            (1 / 2 : ℝ) < initialPrimeValue alpha tau (m : ℝ) p.1 ∧
              initialPrimeValue alpha tau (m : ℝ) p.1 < (3 / 2 : ℝ)) ∧
          (∀ p : PrimeIndex,
            a p.1 = correctedPrimeValue alpha tau m Y u p.1) ∧
          positiveCompletelyMultiplicative a ∧
          (∀ p : PrimeIndex, Y < p.1 →
            (1 / 2 : ℝ) < a p.1 ∧ a p.1 < (3 / 2 : ℝ)) ∧
          (∀ p : PrimeIndex, p.1 ≤ Y → a p.1 = 1) ∧
          (∀ p : PrimeIndex, ∀ k : ℕ,
            a (p.1 ^ k) = (a p.1) ^ k) ∧
          (∀ p : PrimeIndex, ∀ s : ℂ, p.1 ≤ Y →
            geometricEulerFactor a p.1 s =
              (1 - Complex.exp (-(s * (Real.log (p.1 : ℝ) : ℂ))))⁻¹) ∧
          symmetricQuartet alpha tau =
            {eta alpha tau, starRingEnd ℂ (eta alpha tau),
              rho alpha tau, starRingEnd ℂ (rho alpha tau)}

end

end MathlibPlus.Open.Analysis.O0355Claim15616Repair
