import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

noncomputable section

def Index (N : ℕ) := {t : ℕ // t ≤ N}

def Composition (m N : ℕ) := {μ : Fin m → ℕ // ∑ i, μ i = N}

def zeroIndex (N : ℕ) : Index N := ⟨0, Nat.zero_le _⟩

def topIndex (N : ℕ) : Index N := ⟨N, le_rfl⟩

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

def sevenFactorAnnihilator (N : ℕ) (f h k : Index N → ℚ) : Prop :=
  ∀ μ : Composition 7 N,
    blockSum 1 f μ + blockSum 2 h μ + blockSum 3 k μ = 0

structure SevenFactorParameters where
  d₀ : ℚ
  d₁ : ℚ
  d₂ : ℚ
  d₃ : ℚ
  d₄ : ℚ
  d₅ : ℚ
  c₀ : ℚ
  c₁ : ℚ
  c₂ : ℚ
  c₃ : ℚ
  A : ℚ
  B : ℚ

def sevenParameterK (N : ℕ) (p : SevenFactorParameters) : Index N → ℚ :=
  fun t => p.d₀ + p.d₁ * (t.1 : ℚ) + p.d₂ * (t.1 : ℚ) ^ 2 +
    p.d₃ * (t.1 : ℚ) ^ 3 + p.d₄ * (t.1 : ℚ) ^ 4 +
    p.d₅ * (t.1 : ℚ) ^ 5

def sevenParameterH (N : ℕ) (p : SevenFactorParameters) : Index N → ℚ :=
  fun t => p.c₀ + p.c₁ * (t.1 : ℚ) + p.c₂ * (t.1 : ℚ) ^ 2 +
    p.c₃ * (t.1 : ℚ) ^ 3 - 2 * sevenParameterK N p t -
      sevenParameterK N p (reflectIndex N t)

def sevenParameterF (N : ℕ) (p : SevenFactorParameters) : Index N → ℚ :=
  fun t => p.A + p.B * (t.1 : ℚ) -
    4 * sevenParameterH N p t -
    sevenParameterH N p (reflectIndex N t) -
    6 * sevenParameterK N p t -
    4 * sevenParameterK N p (reflectIndex N t)

def sevenEndpoint (N : ℕ) (p : SevenFactorParameters) : Prop :=
  7 * p.A + p.B * (N : ℚ) =
    4 * sevenParameterH N p (topIndex N) +
      10 * sevenParameterH N p (zeroIndex N) +
        15 * sevenParameterK N p (topIndex N) +
          20 * sevenParameterK N p (zeroIndex N)

def sevenRepresentation (N : ℕ) (p : SevenFactorParameters)
    (f h k : Index N → ℚ) : Prop :=
  (∀ t, k t = sevenParameterK N p t) ∧
    (∀ t, h t = sevenParameterH N p t) ∧
      (∀ t, f t = sevenParameterF N p t) ∧
        sevenEndpoint N p

/-- Claim 26001: the seven-factor annihilators and exactly the displayed
quintic/cubic normal forms, endpoint condition, and unique parameters. -/
def claim26001 : Prop :=
  ∀ (N : ℕ), 7 ≤ N →
    (∀ (f h k : Index N → ℚ),
      sevenFactorAnnihilator N f h k →
        ∃! p : SevenFactorParameters,
          sevenRepresentation N p f h k) ∧
    (∀ (p : SevenFactorParameters) (f h k : Index N → ℚ),
      sevenRepresentation N p f h k →
        sevenFactorAnnihilator N f h k)

end

end MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001
