import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Batch_01a0032b

noncomputable section

abbrev PrimeIndex := {p : ℕ // p.Prime}

def primePower (p : PrimeIndex) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (p.1 : ℝ) : ℂ))

def primeCoefficientNormSquared (c : PrimeIndex → ℂ) : ℝ :=
  ∑' p : PrimeIndex, ‖c p‖ ^ 2

def primeSeriesPartial (c : PrimeIndex → ℂ) (F : Finset PrimeIndex) (s : ℂ) : ℂ :=
  F.sum (fun p => c p * primePower p s)

def primeSeriesValue (c : PrimeIndex → ℂ) (s : ℂ) : ℂ :=
  ∑' p : PrimeIndex, c p * primePower p s

def locallyUniformPrimeSeries (c : PrimeIndex → ℂ) (g : ℂ → ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | 1 / 2 < s.re} →
    ∀ ε : ℝ, 0 < ε →
      ∃ F₀ : Finset PrimeIndex,
        ∀ F : Finset PrimeIndex, F₀ ⊆ F →
          ∀ s ∈ K, ‖g s - primeSeriesPartial c F s‖ < ε

/-- Claim 9784: the prime-linear Hilbert space and its locally uniform series. -/
def primeLinearHilbertSpace : Prop :=
  ∀ c : PrimeIndex → ℂ, Summable (fun p => ‖c p‖ ^ 2) →
    ∃ g : ℂ → ℂ,
      (∀ s : ℂ, 1 / 2 < s.re → g s = primeSeriesValue c s) ∧
      locallyUniformPrimeSeries c g

def endpointCoefficient (a b : ℂ) (p : PrimeIndex) : ℂ :=
  primePower p b - primePower p a

def endpointSeries (c : PrimeIndex → ℂ) (a b : ℂ) : ℂ :=
  ∑' p : PrimeIndex, c p * endpointCoefficient a b p

def endpointDualNormSquared (a b : ℂ) : ℝ :=
  (sSup {r : ℝ |
    ∃ c : PrimeIndex → ℂ,
      Summable (fun p => ‖c p‖ ^ 2) ∧
      primeCoefficientNormSquared c ≤ 1 ∧
      r = ‖endpointSeries c a b‖}) ^ 2

/-- Claim 9785: the exact endpoint-functional dual norm. -/
def exactEndpointFunctionalDualNorm : Prop :=
  ∀ (a b : ℂ), 1 / 2 < a.re → 1 / 2 < b.re →
    endpointDualNormSquared a b =
      ∑' p : PrimeIndex, ‖endpointCoefficient a b p‖ ^ 2

/-- Claim 9786: the exact least-norm endpoint displacement and its representer. -/
def exactLeastNormEndpointDisplacement : Prop :=
  ∀ (a b : ℂ), 1 / 2 < a.re → 1 / 2 < b.re →
    let D : ℝ := ∑' p : PrimeIndex, ‖endpointCoefficient a b p‖ ^ 2
    D ≠ 0 →
      ∀ Δ : ℂ, ∃ cstar : PrimeIndex → ℂ,
        Summable (fun p => ‖cstar p‖ ^ 2) ∧
        endpointSeries cstar a b = Δ ∧
        (∀ c : PrimeIndex → ℂ,
          Summable (fun p => ‖c p‖ ^ 2) → endpointSeries c a b = Δ →
            primeCoefficientNormSquared cstar ≤ primeCoefficientNormSquared c) ∧
        (∀ p : PrimeIndex,
          cstar p = Δ * star (endpointCoefficient a b p) / (D : ℂ)) ∧
        primeCoefficientNormSquared cstar = ‖Δ‖ ^ 2 / D

end

end MathlibPlus.Open.Batch_01a0032b
