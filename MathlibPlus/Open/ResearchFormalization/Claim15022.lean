import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a0067d

open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open Classical

namespace MathlibPlus.Open.ResearchFormalization.Claim15022

/-- The transition scale used by the C-0184/C-0214 model. -/
private noncomputable def transitionScale (k L : ℕ) : ℝ :=
  Real.rpow (L : ℝ) (1 / (2 * (k : ℝ)))

/-- A local divisor list is a multiset: repeated divisor multiplicities are
retained when projected to the real axis. -/
private noncomputable def projectedHeight (D : Multiset ℂ) (L : ℕ) (x : ℝ) : ℝ :=
  (D.map (fun ρ => min (L : ℝ) (1 / |x - ρ.re|))).sum

private def projectedNeighborhood (D : Multiset ℂ) (L : ℕ) : Set ℝ :=
  {x : ℝ | ∃ ρ, ρ ∈ D ∧ |x - ρ.re| ≤ 1 / (L : ℝ)}

private noncomputable def prunedSet (D : Multiset ℂ) (L : ℕ) (ε : ℝ)
    (x₁ x₂ : ℝ) : Set ℝ :=
  Set.Icc x₁ x₂ ∩
    (projectedNeighborhood D L ∪
      {x : ℝ | projectedHeight D L x > ε * L})

private noncomputable def realLength (E : Set ℝ) : ℝ :=
  ENNReal.toReal (volume E)

/-- An interval-like set is allowed to be open, closed, or half-open. -/
private def intervalLike (E : Set ℝ) : Prop :=
  ∀ x ∈ E, ∀ z ∈ E, ∀ y : ℝ, x ≤ y → y ≤ z → y ∈ E

/-- Exact finite-component carrier, rather than an unconstrained component
count: the pieces are pairwise disjoint interval-like subsets whose union is
`E`. -/
private def atMostIntervalComponents (E : Set ℝ) (N : ℕ) : Prop :=
  ∃ m : ℕ, m ≤ N ∧
    ∃ C : Fin m → Set ℝ,
      E = ⋃ i : Fin m, C i ∧
        (∀ i, (C i).Nonempty ∧ intervalLike (C i)) ∧
        (∀ i j, i ≠ j → Disjoint (C i) (C j))

private def divisorCardinalityBound (k : ℕ) (d : ℕ → ℕ)
    (D : ℕ → Multiset ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ L : ℕ in atTop,
      ((D L).card : ℝ) ≤
        C * ((d L : ℝ) + transitionScale k L *
          Real.log (transitionScale k L))

private def intervalWidthBound (k : ℕ) (x₁ x₂ : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ L : ℕ in atTop,
      x₁ L ≤ x₂ L ∧ x₂ L - x₁ L ≤ C * transitionScale k L

private def pruningLengthBound (k : ℕ) (d : ℕ → ℕ)
    (D : ℕ → Multiset ℂ) (ε : ℝ) (x₁ x₂ : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ L : ℕ in atTop,
      realLength (prunedSet (D L) L ε (x₁ L) (x₂ L)) ≤
        C * ((d L : ℝ) + transitionScale k L *
          Real.log (transitionScale k L)) *
          Real.log ((L : ℝ) * transitionScale k L) /
          (ε * (L : ℝ))

private def pruningComponentBound (k : ℕ) (d : ℕ → ℕ)
    (D : ℕ → Multiset ℂ) (ε : ℝ) (x₁ x₂ : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ L : ℕ in atTop,
      atMostIntervalComponents
        (prunedSet (D L) L ε (x₁ L) (x₂ L))
        (Nat.ceil
          (C * ((d L : ℝ) + transitionScale k L *
            Real.log (transitionScale k L))))

/-- Claim 15022.  The divisor family is the finite multiset supplied by the
local logarithmic-derivative formula (hence its cardinality is tied to the
profile degree and local Xi divisors).  The assertion is uniform in the
locations of that multiset, but the removed set is the actual transition
interval `Icc (x₁ L) (x₂ L)`, not an arbitrary set. -/
def claim15022 : Prop :=
  ∀ (P : ℕ → Polynomial ℝ) (a : ℕ → ℕ → ℝ) (d : ℕ → ℕ)
    (B : ℕ → ℝ) (k : ℕ) (D : ℕ → Multiset ℂ)
    (ε : ℝ) (x₁ x₂ : ℕ → ℝ),
    MathlibPlus.Open.ResearchFormalization.admissiblePolynomialProfileClass
      P a d B k →
      0 < ε →
      divisorCardinalityBound k d D →
      intervalWidthBound k x₁ x₂ →
      pruningLengthBound k d D ε x₁ x₂ ∧
      (fun L : ℕ =>
        realLength (prunedSet (D L) L ε (x₁ L) (x₂ L))) =o[atTop]
        (fun L : ℕ => transitionScale k L) ∧
      pruningComponentBound k d D ε x₁ x₂

end MathlibPlus.Open.ResearchFormalization.Claim15022
