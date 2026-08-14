import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Research.R3132

abbrev Support (m : ℕ) := {S : Finset (Fin m) // S.Nonempty}

abbrev SupportVector (m : ℕ) (α : Type*) := Support m → α

def pairCover (m : ℕ) (z : SupportVector m ℝ) (i j : Fin m) : ℝ :=
  ∑ S : Support m,
    if (i ∈ S.1 ∧ j ∉ S.1) ∨ (j ∈ S.1 ∧ i ∉ S.1) then z S else 0

def intermediateCover (m k : ℕ) (z : SupportVector m ℝ)
    (I : Finset (Fin m)) : ℝ :=
  ∑ S : Support m,
    if 2 ≤ (S.1 ∩ I).card ∧ (S.1 ∩ I).card ≤ k - 1 then z S else 0

def memberLoad (m : ℕ) (z : SupportVector m ℝ) (i : Fin m) : ℝ :=
  ∑ S : Support m, if i ∈ S.1 then z S else 0

def nonnegative (m : ℕ) (z : SupportVector m ℝ) : Prop :=
  ∀ S, 0 ≤ z S

def fractionalFeasible (m k : ℕ) (z : SupportVector m ℝ) : Prop :=
  nonnegative m z ∧
    (∀ I : Finset (Fin m), I.card = k → 1 ≤ intermediateCover m k z I) ∧
    (∀ i j : Fin m, i ≠ j → 1 ≤ pairCover m z i j)

def lambda (k : ℕ) : ℝ :=
  max 2 ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - k - 2))

def uniformWeight (m k : ℕ) : SupportVector m ℝ :=
  fun _ => lambda k / (2 : ℝ) ^ m

def pairSupportCount (m : ℕ) (i j : Fin m) : ℕ :=
  Fintype.card {S : Support m //
    (i ∈ S.1 ∧ j ∉ S.1) ∨ (j ∈ S.1 ∧ i ∉ S.1)}

def intermediateSupportCount (m k : ℕ) (I : Finset (Fin m)) : ℕ :=
  Fintype.card {S : Support m //
    2 ≤ (S.1 ∩ I).card ∧ (S.1 ∩ I).card ≤ k - 1}

def memberSupportCount (m : ℕ) (i : Fin m) : ℕ :=
  Fintype.card {S : Support m // i ∈ S.1}

def claim46054 : Prop :=
  ∀ m k : ℕ, 3 ≤ k → k ≤ m →
    (∀ i j : Fin m, i ≠ j →
      pairSupportCount m i j = 2 ^ (m - 1) ∧
      pairCover m (uniformWeight m k) i j = lambda k / 2 ∧
      1 ≤ lambda k / 2) ∧
    (∀ I : Finset (Fin m), I.card = k →
      intermediateSupportCount m k I = (2 ^ k - k - 2) * 2 ^ (m - k) ∧
      intermediateCover m k (uniformWeight m k) I =
        lambda k * ((2 : ℝ) ^ k - k - 2) / (2 : ℝ) ^ k ∧
      1 ≤ lambda k * ((2 : ℝ) ^ k - k - 2) / (2 : ℝ) ^ k) ∧
    (∀ i : Fin m,
      memberSupportCount m i = 2 ^ (m - 1) ∧
      memberLoad m (uniformWeight m k) i = lambda k / 2) ∧
    lambda 3 / 2 = 4 / 3 ∧
    (∀ h : 4 ≤ k, lambda k / 2 = 1)

def canonicalMember (m : ℕ) (i : Fin m) : Finset (Support m) :=
  Finset.univ.filter (fun S => i ∈ S.1)

def canonicalMultiplicityLoad (m r : ℕ) : ℕ := r * 2 ^ (m - 1)

def canonicalPairSeparated (m : ℕ) : Prop :=
  ∀ i j : Fin m, i ≠ j →
    ∃ S : Support m, (i ∈ S.1 ∧ j ∉ S.1) ∨ (j ∈ S.1 ∧ i ∉ S.1)

def canonicalIntermediateWitness (m k : ℕ) : Prop :=
  ∀ I : Finset (Fin m), I.card = k →
    ∀ i j : Fin m, i ∈ I → j ∈ I → i ≠ j →
      ∃ S : Support m,
        i ∈ S.1 ∧ j ∈ S.1 ∧
          2 ≤ (S.1 ∩ I).card ∧ (S.1 ∩ I).card ≤ k - 1

def claim46056 : Prop :=
  ∀ m k : ℕ, 3 ≤ k → k ≤ m →
    (∀ i : Fin m, (canonicalMember m i).card = 2 ^ (m - 1)) ∧
    (∀ i j : Fin m, i ≠ j → canonicalMember m i ≠ canonicalMember m j) ∧
    canonicalPairSeparated m ∧
    canonicalIntermediateWitness m k ∧
    canonicalMultiplicityLoad m 1 = 2 ^ (m - 1) ∧
    ∀ r : ℕ, canonicalMultiplicityLoad m r = r * 2 ^ (m - 1)

/-- The usual meaning of a fixed-k logarithmic lower bound for the displayed
linear relaxation. -/
def fixedKLogLowerBound (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → k ≤ m →
    ∀ z : SupportVector m ℝ, fractionalFeasible m k z →
      ∃ i : Fin m, c * Real.log (m : ℝ) ≤ memberLoad m z i

def claim46055 : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ¬ fixedKLogLowerBound k ∧
    ∀ m : ℕ, k ≤ m → fractionalFeasible m k (uniformWeight m k) ∧
      ∀ i : Fin m, memberLoad m (uniformWeight m k) i = lambda k / 2

end MathlibPlus.Open.Research.R3132
