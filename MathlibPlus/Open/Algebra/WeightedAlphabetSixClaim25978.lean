import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978

noncomputable section

def Index (N : ℕ) := {t : ℕ // t ≤ N}

def Composition (m N : ℕ) := {μ : Fin m → ℕ // ∑ i, μ i = N}

def zeroIndex (N : ℕ) : Index N := ⟨0, Nat.zero_le _⟩

def reflectIndex (N : ℕ) (t : Index N) : Index N :=
  ⟨N - t.1, Nat.sub_le _ _⟩

def subsetIndex {m N : ℕ} (μ : Composition m N) (I : Finset (Fin m)) : Index N :=
  ⟨∑ i ∈ I, μ.1 i, by
    calc
      ∑ i ∈ I, μ.1 i ≤ ∑ i : Fin m, μ.1 i :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ I)
      _ = N := μ.2⟩

def subsetFamily (m r : ℕ) : Finset (Finset (Fin m)) :=
  ((Finset.univ : Finset (Fin m)).powerset).filter (fun I => I.card = r)

def blockSum {m N : ℕ} (r : ℕ) (g : Index N → ℚ)
    (μ : Composition m N) : ℚ :=
  ∑ I ∈ subsetFamily m r, g (subsetIndex μ I)

def allSubsets (m : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Fin m)).powerset

def mixedDifference {m N : ℕ} (g : Index N → ℚ)
    (μ : Composition m N) : ℚ :=
  ∑ I ∈ allSubsets m,
    (-1 : ℚ) ^ (m - I.card) * g (subsetIndex μ I)

def middleResidual {N : ℕ} (k : Index N → ℚ)
    (μ : Composition 6 N) : ℚ :=
  blockSum 3 k μ - 2 * blockSum 2 k μ + 2 * blockSum 1 k μ

def reflective (N : ℕ) (g : Index N → ℚ) : Prop :=
  ∀ t, g t = g (reflectIndex N t)

def sixFactorAnnihilator (N : ℕ) (f h k : Index N → ℚ) : Prop :=
  reflective N k ∧
    ∀ μ : Composition 6 N,
      blockSum 1 f μ + blockSum 2 h μ + blockSum 3 k μ = 0

def cubicMiddleCandidate (N : ℕ)
    (d₀ d₁ d₂ d₃ : ℚ) : Index N → ℚ :=
  fun t => d₀ + d₁ * (t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ) +
    d₂ * ((t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ)) ^ 2 +
    d₃ * ((t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ)) ^ 3

def quarticPairCandidate (N : ℕ)
    (c₀ c₁ c₂ c₃ c₄ : ℚ) : Index N → ℚ :=
  fun t => c₀ + c₁ * (t.1 : ℚ) + c₂ * (t.1 : ℚ) ^ 2 +
    c₃ * (t.1 : ℚ) ^ 3 + c₄ * (t.1 : ℚ) ^ 4

def coupledPairCandidate (N : ℕ) (k : Index N → ℚ)
    (p₀ p₁ p₂ p₃ : ℚ) : Index N → ℚ :=
  fun t => p₀ + p₁ * (t.1 : ℚ) + p₂ * (t.1 : ℚ) ^ 2 +
    p₃ * (t.1 : ℚ) ^ 3 - 2 * k t

/-- Claim 25978: a nonzero cubic term in `t(N-t)` is detected by the
sixfold fixed-total test, while a quartic pair can pass only with the exact
middle coupling. -/
def claim25978 : Prop :=
  ∀ (N : ℕ), 6 ≤ N →
    (∀ (d₀ d₁ d₂ d₃ : ℚ), d₃ ≠ 0 →
      ∃ μ : Composition 6 N,
        mixedDifference (cubicMiddleCandidate N d₀ d₁ d₂ d₃) μ ≠ 0) ∧
    (∀ (f h k : Index N → ℚ)
      (c₀ c₁ c₂ c₃ c₄ : ℚ),
      sixFactorAnnihilator N f h k → c₄ ≠ 0 →
        (∀ t, h t = quarticPairCandidate N c₀ c₁ c₂ c₃ c₄ t) →
          ∃ (p₀ p₁ p₂ p₃ : ℚ),
            ∀ t, h t = coupledPairCandidate N k p₀ p₁ p₂ p₃ t)

end

end MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25978
