import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26013

noncomputable section

abbrev Coordinate (N : ℕ) := Fin (N + 1)
abbrev Eight := Fin 8

abbrev Composition (N : ℕ) :=
  { μ : Eight → Coordinate N // ∑ i : Eight, (μ i).val = N }

def boundedIndex (N s : ℕ) : Coordinate N :=
  ⟨min s N, Nat.lt_succ_of_le (Nat.min_le_right s N)⟩

def subsetIndex {N : ℕ} (μ : Composition N)
    (S : Finset Eight) : Coordinate N :=
  boundedIndex N (∑ i ∈ S, (μ.1 i).val)

def reflectedIndex {N : ℕ} (t : Coordinate N) : Coordinate N :=
  ⟨N - t.val, Nat.lt_succ_of_le (Nat.sub_le N t.val)⟩

def reflective (N : ℕ) (l : Coordinate N → ℚ) : Prop :=
  ∀ t : Coordinate N, l t = l (reflectedIndex t)

def blockProfile {N : ℕ} (k : ℕ) (μ : Composition N)
    (t : Coordinate N) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight).powersetCard k,
    if subsetIndex μ S = t then 1 else 0

def foldedSubsetIndex {N : ℕ} (μ : Composition N)
    (S : Finset Eight) : Coordinate N :=
  boundedIndex N
    (min (∑ i ∈ S, (μ.1 i).val)
      (N - ∑ i ∈ S, (μ.1 i).val))

def foldedFourProfile {N : ℕ} (μ : Composition N)
    (t : Coordinate N) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight).powersetCard 4,
    if foldedSubsetIndex μ S = t then 1 else 0

def rowPairing {N : ℕ} (f h k l : Coordinate N → ℚ)
    (μ : Composition N) : ℚ :=
  (∑ t : Coordinate N, f t * blockProfile 1 μ t) +
    (∑ t : Coordinate N, h t * blockProfile 2 μ t) +
    (∑ t : Coordinate N, k t * blockProfile 3 μ t) +
    (∑ t : Coordinate N, l t * foldedFourProfile μ t)

def blockSum {N : ℕ} (k : ℕ) (g : Coordinate N → ℚ)
    (μ : Composition N) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight).powersetCard k,
    g (subsetIndex μ S)

def foldedFourSum {N : ℕ} (l : Coordinate N → ℚ)
    (μ : Composition N) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight).powersetCard 4,
    l (foldedSubsetIndex μ S)

def displayedEightFactorEquation {N : ℕ}
    (f h k l : Coordinate N → ℚ) (μ : Composition N) : ℚ :=
  blockSum 1 f μ + blockSum 2 h μ + blockSum 3 k μ + foldedFourSum l μ

def claim26013_exactEightFactorAnnihilatorEquation : Prop :=
  ∀ (N : ℕ) (f h k l : Coordinate N → ℚ),
    reflective N l →
      ((∀ μ : Composition N, rowPairing f h k l μ = 0) ↔
        ∀ μ : Composition N,
          displayedEightFactorEquation f h k l μ = 0)

end

end MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26013
