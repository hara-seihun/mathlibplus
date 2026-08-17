import Mathlib
import MathlibPlus.Combinatorics.StrongOrdering

namespace MathlibPlus.Open.Combinatorics.PrefixOrdering

/-- Claim 48370: distinct reflected unused labels occur at distinct prefix indices. -/
def reflectedPrefixIndicesDistinct_claim48370 : Prop :=
  ∀ (G : Type*) [AddCommGroup G]
    (B : List G) (u v : G) (a b : ℕ),
    MathlibPlus.Combinatorics.strongOrdering B →
    MathlibPlus.Combinatorics.validOrdering B →
    a ≤ B.length →
    b ≤ B.length →
    u ∉ B →
    v ∉ B →
    u ≠ v →
    u + v = -B.sum →
    (B.take a).sum = -u →
    (B.take b).sum = -v →
    a ≠ b

/-- The proper-prefix definition of a simple zero-sum cycle used by R-3706. -/
private def simpleZeroSumCycle {G : Type*} [AddMonoid G]
    (C : List G) : Prop :=
  C.sum = 0 ∧
    ∀ i j : ℕ,
      i < C.length → j < C.length → i ≠ j →
        (C.take i).sum ≠ (C.take j).sum

/-- Claim 48375: the exchanged cut at `b` gives the crossed simple cycles and
its label partition, with the repaired exact-label carrier. -/
def exchangedCutCycles_claim48375 : Prop :=
  ∀ (G : Type*) [AddCommGroup G]
    (B : List G) (u v : G) (a b : ℕ),
    B.Nodup →
    MathlibPlus.Combinatorics.strongOrdering B →
    MathlibPlus.Combinatorics.validOrdering B →
    a ≤ B.length →
    b ≤ B.length →
    u ∉ B →
    v ∉ B →
    u ≠ v →
    u + v = -B.sum →
    (B.take a).sum = -u →
    (B.take b).sum = -v →
    let C_a_minus : List G := B.take a ++ [u]
    let C_a_plus : List G := B.drop a ++ [v]
    let C_b_minus : List G := B.take b ++ [v]
    let C_b_plus : List G := B.drop b ++ [u]
    (simpleZeroSumCycle C_b_minus ∧
      simpleZeroSumCycle C_b_plus ∧
      (∀ x, x ∈ C_b_minus → x ∉ C_b_plus) ∧
      (∀ x, x ∈ C_b_minus ∨ x ∈ C_b_plus ↔
        x ∈ B ∨ x = u ∨ x = v) ∧
      (∀ x, x ∈ C_a_minus → x ∉ C_a_plus) ∧
      (∀ x, x ∈ C_a_minus ∨ x ∈ C_a_plus ↔
        x ∈ B ∨ x = u ∨ x = v) ∧
      (B.take b).sum + v = 0 ∧
      (B.sum - (B.take b).sum) + u = B.sum + v + u ∧
      B.sum + v + u = 0)

/-- Claim 48377: after orienting the reflected cuts with `a < b`, the four
crossed cells are simple zero-sum cycles and both rows partition the augmented
label set. -/
def crossedCycleRectangle_claim48377 : Prop :=
  ∀ (G : Type*) [AddCommGroup G]
    (B : List G) (u v : G) (a b : ℕ),
    B.Nodup →
    MathlibPlus.Combinatorics.strongOrdering B →
    MathlibPlus.Combinatorics.validOrdering B →
    a ≤ B.length →
    b ≤ B.length →
    a < b →
    u ∉ B →
    v ∉ B →
    u ≠ v →
    u + v = -B.sum →
    (B.take a).sum = -u →
    (B.take b).sum = -v →
    let L : List G := B.take a
    let M : List G := (B.drop a).take (b - a)
    let R : List G := B.drop b
    let C₁ : List G := L ++ [u]
    let C₂ : List G := M ++ R ++ [v]
    let C₃ : List G := L ++ M ++ [v]
    let C₄ : List G := R ++ [u]
    let sameAugmentedPartition : List G → List G → Prop := fun C D =>
      (∀ x, x ∈ C → x ∉ D) ∧
        (∀ x, x ∈ C ∨ x ∈ D ↔ x ∈ B ∨ x = u ∨ x = v)
    B = L ++ M ++ R ∧
      L.sum = -u ∧
      M.sum = u - v ∧
      R.sum = -u ∧
      simpleZeroSumCycle C₁ ∧
      simpleZeroSumCycle C₂ ∧
      simpleZeroSumCycle C₃ ∧
      simpleZeroSumCycle C₄ ∧
      sameAugmentedPartition C₁ C₂ ∧
      sameAugmentedPartition C₃ C₄

end MathlibPlus.Open.Combinatorics.PrefixOrdering
