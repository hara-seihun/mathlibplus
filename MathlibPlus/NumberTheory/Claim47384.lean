import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace MathlibPlus.NumberTheory.Claim47384

/-!
Formalization of the exact stationary signed-return-word obstruction from
admitted claim 47384 (locator `R-2893`).  The coefficients are integer-valued;
the weighted-tail clearing lemma connects them to the displayed rational tail
identity without asserting any broader fibre conclusion.
-/

def returnCoefficient (h : ℕ) (ε : Fin h → ℤ) : ℤ :=
  ∑ i : Fin h, ε i * (2 : ℤ) ^ (h - i.1 - 1)

def returnConstant (h : ℕ) (ε : Fin h → ℤ) : ℤ :=
  ∑ i : Fin h, (i.1 + 1 : ℤ) * ε i * (2 : ℤ) ^ (h - i.1 - 1)

def signedWord (h : ℕ) (ε : Fin h → ℤ) : Prop :=
  ∀ i, ε i = 1 ∨ ε i = -1

def weightedTail (N h : ℕ) (ε : Fin h → ℤ) : ℚ :=
  ∑ i : Fin h,
    (ε i : ℚ) * ((N + i.1 + 1 : ℕ) : ℚ) /
      (2 : ℚ) ^ (N + i.1 + 1)

lemma returnCoefficient_succ (h : ℕ) (ε : Fin (h + 1) → ℤ) :
    returnCoefficient (h + 1) ε =
      2 * returnCoefficient h (fun i => ε i.castSucc) + ε (Fin.last h) := by
  simp only [returnCoefficient, Fin.sum_univ_castSucc]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i.val < h := i.isLt
    simp only [Fin.val_castSucc]
    rw [show h + 1 - i.val - 1 = (h - i.val - 1) + 1 by omega]
    rw [pow_succ]
    ring
  · simp

lemma odd_returnCoefficient_of_signed :
    ∀ n : ℕ, ∀ ε : Fin (n + 1) → ℤ,
      signedWord (n + 1) ε → Odd (returnCoefficient (n + 1) ε) := by
  intro n
  induction n with
  | zero =>
      intro ε hε
      have hsign := hε ⟨0, by omega⟩
      have hC : returnCoefficient (0 + 1) ε = ε ⟨0, by omega⟩ := by
        simp [returnCoefficient]
      rw [hC]
      rcases hsign with h | h
      · rw [h]
        exact odd_one
      · rw [h]
        exact ⟨-1, by ring⟩
  | succ n ih =>
      intro ε hε
      rw [returnCoefficient_succ (n + 1) ε]
      have hprev : Odd (returnCoefficient (n + 1) (fun i => ε i.castSucc)) :=
        ih (fun i => ε i.castSucc) (fun i => hε i.castSucc)
      have heven : Even (2 * returnCoefficient (n + 1) (fun i => ε i.castSucc)) :=
        even_two_mul _
      have hlast : Odd (ε (Fin.last (n + 1))) := by
        rcases hε (Fin.last (n + 1)) with h | h
        · rw [h]
          exact odd_one
        · rw [h]
          exact ⟨-1, by ring⟩
      exact heven.add_odd hlast

lemma returnCoefficient_cast (h : ℕ) (ε : Fin h → ℤ) :
    (returnCoefficient h ε : ℚ) = ∑ i : Fin h,
      (ε i : ℚ) * (2 : ℚ) ^ (h - i.1 - 1) := by
  simp [returnCoefficient, Int.cast_sum, Int.cast_mul, Int.cast_pow]

lemma returnConstant_cast (h : ℕ) (ε : Fin h → ℤ) :
    (returnConstant h ε : ℚ) = ∑ i : Fin h,
      ((i.1 + 1 : ℕ) : ℚ) * (ε i : ℚ) *
        (2 : ℚ) ^ (h - i.1 - 1) := by
  simp [returnConstant, Int.cast_sum, Int.cast_mul, Int.cast_pow]

lemma weightedTail_cleared_term (N h : ℕ) (i : Fin h) (e : ℤ) :
    (2 : ℚ) ^ (N + h) *
        ((e : ℚ) * ((N + i.1 + 1 : ℕ) : ℚ) /
          (2 : ℚ) ^ (N + i.1 + 1)) =
      (N : ℚ) * (e : ℚ) * (2 : ℚ) ^ (h - i.1 - 1) +
        ((i.1 + 1 : ℕ) : ℚ) * (e : ℚ) *
          (2 : ℚ) ^ (h - i.1 - 1) := by
  have hi : i.1 < h := i.isLt
  have hexp : N + h = (N + i.1 + 1) + (h - i.1 - 1) := by omega
  rw [hexp, pow_add]
  have hpow : (2 : ℚ) ^ (N + i.1 + 1) ≠ 0 := by positivity
  rw [div_eq_mul_inv]
  calc
    ((2 : ℚ) ^ (N + i.1 + 1) * (2 : ℚ) ^ (h - i.1 - 1)) *
          ((e : ℚ) * ((N + i.1 + 1 : ℕ) : ℚ) *
            ((2 : ℚ) ^ (N + i.1 + 1))⁻¹) =
        (e : ℚ) * ((N + i.1 + 1 : ℕ) : ℚ) *
          (2 : ℚ) ^ (h - i.1 - 1) *
          ((2 : ℚ) ^ (N + i.1 + 1) *
            ((2 : ℚ) ^ (N + i.1 + 1))⁻¹) := by ring
    _ = (e : ℚ) * ((N + i.1 + 1 : ℕ) : ℚ) *
          (2 : ℚ) ^ (h - i.1 - 1) := by
      rw [mul_inv_cancel₀ hpow, mul_one]
    _ = (N : ℚ) * (e : ℚ) * (2 : ℚ) ^ (h - i.1 - 1) +
        ((i.1 + 1 : ℕ) : ℚ) * (e : ℚ) *
          (2 : ℚ) ^ (h - i.1 - 1) := by
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

lemma weightedTail_cleared (N h : ℕ) (ε : Fin h → ℤ) :
    (2 : ℚ) ^ (N + h) * weightedTail N h ε =
      (N : ℚ) * (returnCoefficient h ε : ℚ) +
        (returnConstant h ε : ℚ) := by
  rw [weightedTail, Finset.mul_sum, returnCoefficient_cast, returnConstant_cast]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [mul_assoc] using weightedTail_cleared_term N h i (ε i)

lemma weightedTail_eq_zero_iff (N h : ℕ) (ε : Fin h → ℤ) :
    weightedTail N h ε = 0 ↔
      (N : ℚ) * (returnCoefficient h ε : ℚ) +
        (returnConstant h ε : ℚ) = 0 := by
  have hpow : (2 : ℚ) ^ (N + h) ≠ 0 := by positivity
  constructor
  · intro ht
    rw [← weightedTail_cleared, ht, mul_zero]
  · intro heq
    have hmul : (2 : ℚ) ^ (N + h) * weightedTail N h ε = 0 := by
      rw [weightedTail_cleared, heq]
    exact (mul_eq_zero.mp hmul).resolve_left hpow

/-- A fixed signed return word has an odd, hence nonzero, coefficient and its
linear return equation has at most one integer start. -/
theorem signedReturnWordObstruction :
    ∀ (h : ℕ) (ε : Fin h → ℤ), 1 ≤ h → signedWord h ε →
      Odd (returnCoefficient h ε) ∧ returnCoefficient h ε ≠ 0 ∧
        ∀ N₁ N₂ : ℤ,
          N₁ * returnCoefficient h ε + returnConstant h ε = 0 →
          N₂ * returnCoefficient h ε + returnConstant h ε = 0 → N₁ = N₂ := by
  intro h ε hh hε
  cases h with
  | zero => omega
  | succ n =>
      have hodd : Odd (returnCoefficient (n + 1) ε) :=
        odd_returnCoefficient_of_signed n ε hε
      have hne : returnCoefficient (n + 1) ε ≠ 0 := by
        intro hzero
        rw [hzero] at hodd
        exact Int.not_odd_zero hodd
      refine ⟨hodd, hne, ?_⟩
      intro N₁ N₂ h₁ h₂
      have hmul : (N₁ - N₂) * returnCoefficient (n + 1) ε = 0 := by
        calc
          (N₁ - N₂) * returnCoefficient (n + 1) ε =
              (N₁ * returnCoefficient (n + 1) ε + returnConstant (n + 1) ε) -
                (N₂ * returnCoefficient (n + 1) ε + returnConstant (n + 1) ε) := by ring
          _ = 0 := by rw [h₁, h₂]; ring
      have hdiff : N₁ - N₂ = 0 := (mul_eq_zero.mp hmul).resolve_right hne
      exact sub_eq_zero.mp hdiff

end MathlibPlus.NumberTheory.Claim47384
