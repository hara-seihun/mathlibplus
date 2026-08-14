import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.StarSunflowerBatch

attribute [local instance] Classical.decEq

noncomputable section

private def edgeSet (m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun e ↦ e.card = 2)

private def star (m : ℕ) (i : Fin m) : Finset (Finset (Fin m)) :=
  (edgeSet m).filter (fun e ↦ i ∈ e)

private def starTrace (m : ℕ) (i : Fin m) (Y : Finset (Finset (Fin m))) :
    Finset (Finset (Fin m)) :=
  star m i ∩ Y

private def tracesInjective (m : ℕ) (Y : Finset (Finset (Fin m))) : Prop :=
  ∀ i j : Fin m, i ≠ j → starTrace m i Y ≠ starTrace m j Y

/-- Claim 46186: injective traces of the stars force at least half as many
selected edges as the number of vertices less one. -/
def claim46186 : Prop :=
  ∀ (m : ℕ) (Y : Finset (Finset (Fin m))),
    Y ⊆ edgeSet m →
      ((∀ i j : Fin m,
          i ≠ j → starTrace m i Y ≠ starTrace m j Y) →
        (Y.card : ℝ) ≥ ((m - 1 : ℕ) : ℝ) / 2) ∧
      (∀ i : Fin m,
        starTrace m i Y = ∅ ↔
          ∀ e : Finset (Fin m), e ∈ Y → i ∉ e) ∧
      (∀ i j : Fin m,
        (∀ e : Finset (Fin m), e ∈ Y → i ∉ e) →
        (∀ e : Finset (Fin m), e ∈ Y → j ∉ e) →
        starTrace m i Y = starTrace m j Y)

private abbrev BlockEdge (g M : ℕ) := Fin g × Finset (Fin M)

private def blockEdgeSet (g M : ℕ) : Finset (BlockEdge g M) :=
  Finset.univ.filter (fun p ↦ p.2.card = 2)

private def productMember (g M : ℕ) (v : Fin g → Fin M) :
    Finset (BlockEdge g M) :=
  (blockEdgeSet g M).filter (fun p ↦ v p.1 ∈ p.2)

private def productFamily (g M : ℕ) :
    Finset (Finset (BlockEdge g M)) :=
  Finset.univ.image (productMember g M)

private def wordTrace (g M : ℕ) (v : Fin g → Fin M)
    (Y : Finset (BlockEdge g M)) : Finset (BlockEdge g M) :=
  productMember g M v ∩ Y

private def sunflower (S : Finset (Finset α)) : Prop :=
  ∃ core : Finset α,
    ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = core

private def untouchedLocal (g M : ℕ) (Y : Finset (BlockEdge g M)) (r : Fin g) :
    Finset (Fin M) :=
  Finset.univ.filter (fun v ↦
    ∀ p : BlockEdge g M, p ∈ Y → p.1 ≠ r ∨ v ∉ p.2)

/-- Claim 46189: the product of `g` disjoint complete-graph blocks has the
stated word-indexed family size and uniformity. -/
def claim46189 : Prop :=
  ∀ g M : ℕ,
    (productFamily g M).card = M ^ g ∧
      ∀ v : Fin g → Fin M,
        (productMember g M v).card = g * (M - 1)

/-- Claim 46192: three distinct words have nonconstant pair intersections, and
therefore no subfamily of size at least three is a sunflower. -/
def claim46192 : Prop :=
  ∀ g M : ℕ,
    (∀ a b c : Fin g → Fin M,
      a ≠ b → a ≠ c → b ≠ c →
        ¬(productMember g M a ∩ productMember g M b =
            productMember g M a ∩ productMember g M c ∧
          productMember g M a ∩ productMember g M b =
            productMember g M b ∩ productMember g M c)) ∧
      ∀ k : ℕ, 3 ≤ k →
        ∀ S : Finset (Finset (BlockEdge g M)),
          S.card = k →
          (∀ A ∈ S, A ∈ productFamily g M) →
          ¬ sunflower S

/-- Claim 46194: an injective coordinate set leaves at most one untouched
local vertex in each block, giving the `n/2` lower bound. -/
def claim46194 : Prop :=
  ∀ g M : ℕ,
    ∀ Y : Finset (BlockEdge g M),
      Y ⊆ blockEdgeSet g M →
      (∀ a b : Fin g → Fin M, a ≠ b →
        wordTrace g M a Y ≠ wordTrace g M b Y) →
      (∀ r : Fin g, (untouchedLocal g M Y r).card ≤ 1) ∧
      (Y.card : ℝ) ≥ (g * (M - 1) : ℝ) / 2

/-- Claim 46199: when the selected coordinates lie in one star, the exact
star-size obstruction and all of its small-size collision cases hold. -/
def claim46199 : Prop :=
  ∀ (m : ℕ) (i : Fin m) (Y : Finset (Finset (Fin m))),
    Y ⊆ star m i →
      (tracesInjective m Y → Y.card = m - 1) ∧
      (Y.card = 0 → ∀ j k : Fin m, starTrace m j Y = starTrace m k Y) ∧
      (Y.card = 1 →
        ∃ j : Fin m, j ≠ i ∧ starTrace m j Y = starTrace m i Y) ∧
      (2 ≤ Y.card → Y.card ≤ m - 2 →
        ∀ j : Fin m,
          j ≠ i →
          (∀ e : Finset (Fin m), e ∈ Y → j ∉ e) →
          starTrace m j Y = ∅) ∧
      tracesInjective m (star m i)

end
end MathlibPlus.Open.Combinatorics.StarSunflowerBatch
