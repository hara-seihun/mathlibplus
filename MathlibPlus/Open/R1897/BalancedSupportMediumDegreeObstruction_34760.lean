import MathlibPlus.Open.Combinatorics.IncidenceSunflower

namespace MathlibPlus.Open.R1897

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

private abbrev Ground (m s : ℕ) :=
  {A : Finset (Fin m) // A.card = s}

private def balancedMember (m s : ℕ) (i : Fin m) : Finset (Ground m s) :=
  Finset.univ.filter (fun A => i ∈ A.1)

private def balancedFamily (m s : ℕ) : Finset (Finset (Ground m s)) :=
  Finset.univ.image (balancedMember m s)

private def mediumDegreeFailure
    (m s : ℕ) (𝓕 : Finset (Finset (Ground m s))) : Prop :=
  ∀ D E : ℕ, D < s → s < m - E →
    ∀ x ∈ MathlibPlus.Open.Combinatorics.groundCoordinates 𝓕,
      D < MathlibPlus.Open.Combinatorics.incidenceDegree 𝓕 x ∧
        E < m - MathlibPlus.Open.Combinatorics.incidenceDegree 𝓕 x

private def balancedConstruction (m s : ℕ) : Prop :=
  let 𝓕 := balancedFamily m s
  𝓕.card = m ∧
    MathlibPlus.Open.Combinatorics.isNUniform 𝓕
      (Nat.choose (m - 1) (s - 1)) ∧
    MathlibPlus.Open.Combinatorics.isKSunflowerFree 𝓕 3 ∧
    (∀ i j k : Fin m,
      i ≠ j → i ≠ k → j ≠ k →
        ∃ A : Ground m s,
          i ∈ A.1 ∧ j ∈ A.1 ∧ k ∉ A.1) ∧
    (∀ x ∈ MathlibPlus.Open.Combinatorics.groundCoordinates 𝓕,
      MathlibPlus.Open.Combinatorics.incidenceDegree 𝓕 x = s) ∧
    (∀ x : Ground m s,
      Finset.univ.filter (fun i : Fin m => x ∈ balancedMember m s i) = x.1) ∧
    mediumDegreeFailure m s 𝓕

/-- Claim 34760: all `s`-subset coordinates give the balanced uniform,
    three-sunflower-free incidence obstruction, and `s = floor(m/2)` puts
    every coordinate strictly between any chosen rare and near-common bounds. -/
def claim34760_balancedSupportMediumDegreeObstruction : Prop :=
  (∀ m s : ℕ, 2 ≤ s → s ≤ m - 1 →
    balancedConstruction m s) ∧
  (∀ m : ℕ, 4 ≤ m →
    let s := m / 2
    2 ≤ s ∧ s ≤ m - 1 ∧ balancedConstruction m s)

end

end MathlibPlus.Open.R1897
