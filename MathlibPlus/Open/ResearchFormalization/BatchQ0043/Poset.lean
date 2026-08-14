import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0043

noncomputable section
open scoped BigOperators

structure FiniteRankedPoset (P : Type*) [PartialOrder P] [Fintype P] where
  rank : P → ℕ
  topRank : ℕ
  rank_le_top : ∀ x, rank x ≤ topRank
  rank_lt_of_lt : ∀ {x y}, x < y → rank x < rank y
  rank_cover : ∀ {x y}, x < y → (¬ ∃ z, x < z ∧ z < y) → rank y = rank x + 1

def IsCover {P : Type*} [PartialOrder P] (x y : P) : Prop :=
  x < y ∧ ¬ ∃ z, x < z ∧ z < y

abbrev RankLevel {P : Type*} [PartialOrder P] [Fintype P]
    (R : FiniteRankedPoset P) (r : ℕ) := {x : P // R.rank x = r}

def CoverSupported {P : Type*} [PartialOrder P]
    {K : Type*} [Zero K] (w : P → P → K) : Prop :=
  ∀ x y, ¬ IsCover x y → w x y = 0

def PositiveCoverWeights {P : Type*} [PartialOrder P]
    (n : P → P → ℕ) : Prop :=
  (∀ x y, IsCover x y → 0 < n x y) ∧
    (∀ x y, ¬ IsCover x y → n x y = 0)

def raise {P : Type*} [PartialOrder P] [Fintype P]
    {K : Type*} [CommSemiring K]
    (R : FiniteRankedPoset P) (w : P → P → K) (r : ℕ) :
    (RankLevel R r → K) →ₗ[K] (RankLevel R (r + 1) → K) := by
  classical
  let f : (RankLevel R r → K) → (RankLevel R (r + 1) → K) := fun v y =>
    ∑ x : RankLevel R r, if IsCover x.1 y.1 then w x.1 y.1 * v x else 0
  refine { toFun := f, map_add' := ?_, map_smul' := ?_ }
  · intro v u
    funext y
    dsimp [f]
    calc
      (∑ x : RankLevel R r,
          if IsCover x.1 y.1 then w x.1 y.1 * (v x + u x) else 0) =
          ∑ x : RankLevel R r,
            ((if IsCover x.1 y.1 then w x.1 y.1 * v x else 0) +
              (if IsCover x.1 y.1 then w x.1 y.1 * u x else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : IsCover x.1 y.1
            · simp [h, mul_add]
            · simp [h]
      _ = (∑ x : RankLevel R r,
          if IsCover x.1 y.1 then w x.1 y.1 * v x else 0) +
          ∑ x : RankLevel R r,
            if IsCover x.1 y.1 then w x.1 y.1 * u x else 0 := by
            rw [Finset.sum_add_distrib]
  · intro a v
    funext y
    dsimp [f]
    calc
      (∑ x : RankLevel R r,
          if IsCover x.1 y.1 then w x.1 y.1 * (a • v) x else 0) =
          ∑ x : RankLevel R r,
            a * (if IsCover x.1 y.1 then w x.1 y.1 * v x else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : IsCover x.1 y.1
            · simp [h, mul_left_comm]
            · simp [h]
      _ = a * (∑ x : RankLevel R r,
          if IsCover x.1 y.1 then w x.1 y.1 * v x else 0) := by
            rw [Finset.mul_sum]

def raisePow {P : Type*} [PartialOrder P] [Fintype P]
    {K : Type*} [CommSemiring K]
    (R : FiniteRankedPoset P) (w : P → P → K) :
    (r k : ℕ) → (RankLevel R r → K) →ₗ[K] (RankLevel R (r + k) → K)
  | _, 0 => LinearMap.id
  | r, k + 1 => (raise R w (r + k)).comp (raisePow R w r k)

def Lefschetz {P : Type*} [PartialOrder P] [Fintype P]
    {K : Type*} [CommSemiring K]
    (R : FiniteRankedPoset P) (w : P → P → K) : Prop :=
  (CoverSupported w) ∧
    ∀ r, 2 * r ≤ R.topRank →
      Function.Bijective (raisePow R w r (R.topRank - 2 * r))

def claim16100 : Prop :=
  ∀ {K : Type*} [Field K] [CharZero K]
    {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P]
    (R : FiniteRankedPoset P),
    (∃ w : P → P → K, Lefschetz R w) →
      ∃ n : P → P → ℕ,
        PositiveCoverWeights n ∧
        Lefschetz R (fun x y => (n x y : K))

end
end MathlibPlus.Open.ResearchFormalization.BatchQ0043
