import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25975

noncomputable section

/-- The finite interval `{0, ..., N}` used by the block functionals. -/
def Index (N : ℕ) := {t : ℕ // t ≤ N}

/-- A nonnegative `m`-part composition of the fixed total `N`. -/
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

def reflective (N : ℕ) (g : Index N → ℚ) : Prop :=
  ∀ t, g t = g (reflectIndex N t)

def sixFactorAnnihilator (N : ℕ) (f h k : Index N → ℚ) : Prop :=
  reflective N k ∧
    ∀ μ : Composition 6 N,
      blockSum 1 f μ + blockSum 2 h μ + blockSum 3 k μ = 0

structure SixFactorParameters where
  d₀ : ℚ
  d₁ : ℚ
  d₂ : ℚ
  c₀ : ℚ
  c₁ : ℚ
  c₂ : ℚ
  c₃ : ℚ
  A : ℚ
  B : ℚ

def zCoordinate (N : ℕ) (t : Index N) : ℚ :=
  (t.1 : ℚ) * ((N - t.1 : ℕ) : ℚ)

def sixParameterK (N : ℕ) (p : SixFactorParameters) : Index N → ℚ :=
  fun t => p.d₀ + p.d₁ * zCoordinate N t +
    p.d₂ * (zCoordinate N t) ^ 2

def sixParameterH (N : ℕ) (p : SixFactorParameters) : Index N → ℚ :=
  fun t => p.c₀ + p.c₁ * (t.1 : ℚ) + p.c₂ * (t.1 : ℚ) ^ 2 +
    p.c₃ * (t.1 : ℚ) ^ 3 - 2 * sixParameterK N p t

def sixParameterF (N : ℕ) (p : SixFactorParameters) : Index N → ℚ :=
  fun t => p.A + p.B * (t.1 : ℚ) -
    3 * sixParameterH N p t -
    sixParameterH N p (reflectIndex N t) -
    6 * sixParameterK N p t

def sixEndpoint (N : ℕ) (p : SixFactorParameters) : Prop :=
  6 * p.A + p.B * (N : ℚ) =
    3 * sixParameterH N p (topIndex N) +
      6 * sixParameterH N p (zeroIndex N) +
        16 * sixParameterK N p (zeroIndex N)

/-- Claim 25975: the displayed endpoint equation is the sole compatibility
condition for the listed six-factor functionals. -/
def claim25975 : Prop :=
  ∀ (N : ℕ), 6 ≤ N →
    ∀ p : SixFactorParameters,
      sixEndpoint N p →
        sixFactorAnnihilator N (sixParameterF N p)
          (sixParameterH N p) (sixParameterK N p)

end

end MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25975
