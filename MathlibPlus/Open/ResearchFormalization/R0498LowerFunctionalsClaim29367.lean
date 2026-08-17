import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0498LowerFunctionals

open Classical
open scoped BigOperators
noncomputable section

/-- The sum of the entries indexed by a subset of the ten factor positions. -/
def tenSubsetSum (μ : Fin 10 → ℕ) (I : Finset (Fin 10)) : ℕ :=
  ∑ i ∈ I, μ i

/-- The subset-sum block of cardinality `r` for a functional on the exact
nonnegative subset-sum carrier. -/
def tenSubsetBlockSum (r : ℕ) (g : ℕ → ℚ) (μ : Fin 10 → ℕ) : ℚ :=
  ∑ I ∈ (Finset.univ : Finset (Fin 10)).powerset.filter (fun I => I.card = r),
    g (tenSubsetSum μ I)

/-- The symmetric-octic carrier for the middle block on the range used by a
fixed-total ten-factor annihilator. -/
def symmetricOcticOn (N : ℕ) (m : ℕ → ℚ) : Prop :=
  ∃ d₀ d₁ d₂ d₃ d₄ : ℚ,
    ∀ t : ℕ, t ≤ N →
      let z : ℚ := (t : ℚ) * ((N - t : ℕ) : ℚ)
      m t = d₀ + d₁ * z + d₂ * z ^ 2 + d₃ * z ^ 3 + d₄ * z ^ 4

/-- The concrete stable ten-factor annihilator carrier.  The five functions
are the singleton, pair, triple, four-subset, and self-reciprocal five-subset
functionals; only subset sums of a ten-tuple of total `N` are used. -/
def stableTenFactorAnnihilator (N : ℕ)
    (f h k l m : ℕ → ℚ) : Prop :=
  symmetricOcticOn N m ∧
    (∀ μ : Fin 10 → ℕ,
      (∑ i : Fin 10, μ i) = N →
        tenSubsetBlockSum 1 f μ + tenSubsetBlockSum 2 h μ +
            tenSubsetBlockSum 3 k μ + tenSubsetBlockSum 4 l μ +
            tenSubsetBlockSum 5 m μ = 0)

/-- The coupled lower-block equations from the triangular ten-factor
classification. -/
def tenFactorLowerBlockEquations (N : ℕ)
    (f h k l m : ℕ → ℚ)
    (p₇ p₅ p₃ : Polynomial ℚ) : Prop :=
  ∀ t : ℕ, t ≤ N →
    l t = Polynomial.eval (t : ℚ) p₇ - 2 * m t ∧
    k t = Polynomial.eval (t : ℚ) p₅ - 3 * l t - l (N - t) - 6 * m t ∧
    h t = Polynomial.eval (t : ℚ) p₃ - 5 * k t - k (N - t) -
      10 * l t - 5 * l (N - t) - 20 * m t

/-- The lower functional representation with the three exact degree bounds. -/
def tenFactorLowerBlockRepresentation (N : ℕ)
    (f h k l m : ℕ → ℚ)
    (p₇ p₅ p₃ : Polynomial ℚ) : Prop :=
  p₇.natDegree ≤ 7 ∧ p₅.natDegree ≤ 5 ∧ p₃.natDegree ≤ 3 ∧
    tenFactorLowerBlockEquations N f h k l m p₇ p₅ p₃

/-- Claim 29367: the septic, quintic, and cubic lower-block directions are
both necessary and arbitrary after the displayed coupling to the higher
blocks.  The final clauses retain the three next-degree failures. -/
def lowerSubsetDegreeBounds_claim29367 : Prop :=
  (∀ N : ℕ, 10 ≤ N →
    ∀ f h k l m : ℕ → ℚ,
      stableTenFactorAnnihilator N f h k l m →
        ∃ p₇ p₅ p₃ : Polynomial ℚ,
          tenFactorLowerBlockRepresentation N f h k l m p₇ p₅ p₃) ∧
  (∀ N : ℕ, 10 ≤ N →
    ∀ p₇ p₅ p₃ : Polynomial ℚ,
      p₇.natDegree ≤ 7 ∧ p₅.natDegree ≤ 5 ∧ p₃.natDegree ≤ 3 →
        ∃ f h k l m : ℕ → ℚ,
          stableTenFactorAnnihilator N f h k l m ∧
            tenFactorLowerBlockEquations N f h k l m p₇ p₅ p₃) ∧
  (∀ N : ℕ, 10 ≤ N →
    ¬ ∃ f h k l : ℕ → ℚ,
      stableTenFactorAnnihilator N f h k l (fun _ => 0) ∧
        tenFactorLowerBlockEquations N f h k l (fun _ => 0)
          0 0 (Polynomial.X ^ 4)) ∧
  (∀ N : ℕ, 10 ≤ N →
    ¬ ∃ f h k l : ℕ → ℚ,
      stableTenFactorAnnihilator N f h k l (fun _ => 0) ∧
        tenFactorLowerBlockEquations N f h k l (fun _ => 0)
          0 (Polynomial.X ^ 6) 0) ∧
  (∀ N : ℕ, 10 ≤ N →
    ¬ ∃ f h k l : ℕ → ℚ,
      stableTenFactorAnnihilator N f h k l (fun _ => 0) ∧
        tenFactorLowerBlockEquations N f h k l (fun _ => 0)
          (Polynomial.X ^ 8) 0 0)

end
end MathlibPlus.Open.ResearchFormalization.R0498LowerFunctionals
