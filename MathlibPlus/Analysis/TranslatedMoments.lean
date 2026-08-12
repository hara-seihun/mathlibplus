import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace MathlibPlus.Analysis.TranslatedMoments

universe u v

/-- The weighted moments used by claim 56114. -/
def moment (ι : Type u) (R : Type v) [Semiring R] [Fintype ι]
    (w r : ι → R) (k : ℕ) : R :=
  ∑ s, w s * (w s * r s) ^ k

/-- The translated moment before expanding the translation parameter. -/
def translatedMoment (ι : Type u) (R : Type v) [Semiring R] [Fintype ι]
    (w r : ι → R) (c : R) (a b : ℕ) : R :=
  ∑ s, w s * (w s * r s) ^ (a - 1) * (w s * r s + c) ^ b

/-- Claim 56114's finite translated-moment expansion, with `c = yW`. -/
theorem translatedMoment_expansion
    (ι : Type u) (R : Type v) [CommSemiring R] [Fintype ι]
    (w r : ι → R) (y W : R) (a b : ℕ) (_ha : 1 ≤ a) :
    translatedMoment ι R w r (y * W) a b =
      ∑ j ∈ Finset.range (b + 1),
        (Nat.choose b j : R) * (y * W) ^ (b - j) *
          moment ι R w r (a - 1 + j) := by
  unfold translatedMoment moment
  simp_rw [add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  let x : R := w s * r s
  have hpow : x ^ (a - 1) * x ^ j = x ^ (a - 1 + j) := by
    rw [← pow_add]
  change w s * x ^ (a - 1) *
      (x ^ j * (y * W) ^ (b - j) * (Nat.choose b j : R)) =
    (Nat.choose b j : R) * (y * W) ^ (b - j) *
      (w s * x ^ (a - 1 + j))
  rw [← hpow]
  ring

/-- On the zero-translation face only the combined moment order remains. -/
theorem translatedMoment_zero
    (ι : Type u) (R : Type v) [CommSemiring R] [Fintype ι]
    (w r : ι → R) (a b : ℕ) (ha : 1 ≤ a) :
    translatedMoment ι R w r 0 a b = moment ι R w r (a + b - 1) := by
  unfold translatedMoment moment
  simp only [add_zero]
  apply Finset.sum_congr rfl
  intro s hs
  calc
    w s * (w s * r s) ^ (a - 1) * (w s * r s) ^ b =
        w s * ((w s * r s) ^ (a - 1) * (w s * r s) ^ b) := by rw [mul_assoc]
    _ = w s * (w s * r s) ^ ((a - 1) + b) := by rw [pow_add]
    _ = w s * (w s * r s) ^ (a + b - 1) := by
      congr 2
      omega

end MathlibPlus.Analysis.TranslatedMoments
