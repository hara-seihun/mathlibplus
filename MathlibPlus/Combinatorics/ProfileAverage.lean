import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace MathlibPlus.Combinatorics.ProfileAverage

-- The source's \mathbb F_5 coordinate is enumerated by `Fin 5` below.
def finToZMod5 (r : Fin 5) : ZMod 5 := (r.val : ℕ)

-- This is additive negation in `ZMod 5`, expressed on the `Fin 5` enumeration.
def negFinToZMod5 (r : Fin 5) : ZMod 5 := (((5 - r.val) % 5 : ℕ) : ZMod 5)

/-- Claim 41433's profile value, with `i` represented by its eight coordinates. -/
def profileValue (f : ZMod 5 → ZMod 7) (r : Fin 5) (i : Fin 8) : ZMod 7 :=
  if i.val % 2 = 1 then f (finToZMod5 r) else f 0 - f (negFinToZMod5 r)

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Claim 41433: the average of the forty profile coordinates is `f(0)/2`. -/
theorem profileAverage (f : ZMod 5 → ZMod 7) :
    (∑ r : Fin 5, ∑ i : Fin 8, profileValue f r i) / (40 : ZMod 7) =
      f 0 / 2 := by
  have h5 : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
  have h8 : (Finset.univ : Finset (Fin 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide
  rw [h5, h8]
  simp [Finset.sum_insert, Finset.sum_singleton, profileValue, finToZMod5,
    negFinToZMod5, div_eq_mul_inv]
  have hn1z : (-(1 : ZMod 5)) = (4 : ZMod 5) := by
    apply (ZMod.natCast_eq_natCast_iff' 4 4 5).2
    rfl
  have hn2z : (-(2 : ZMod 5)) = (3 : ZMod 5) := by
    apply (ZMod.natCast_eq_natCast_iff' 3 3 5).2
    rfl
  have hn3z : (-(3 : ZMod 5)) = (2 : ZMod 5) := by
    apply (ZMod.natCast_eq_natCast_iff' 2 2 5).2
    rfl
  have hn4z : (-(4 : ZMod 5)) = (1 : ZMod 5) := by
    apply (ZMod.natCast_eq_natCast_iff' 1 1 5).2
    rfl
  have h5zero : (5 : ZMod 5) = 0 := ZMod.natCast_self 5
  simp [h5zero, hn1z, hn2z, hn3z, hn4z]
  have h40 : (40 : ZMod 7)⁻¹ = 3 := by
    change ((40 : ℕ) : ZMod 7)⁻¹ = ((3 : ℕ) : ZMod 7)
    apply ZMod.inv_eq_of_mul_eq_one
    change ((40 : ℕ) : ZMod 7) * ((3 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
    rw [← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff' 120 1 7).2
    norm_num
  have h2 : (2 : ZMod 7)⁻¹ = 4 := by
    change ((2 : ℕ) : ZMod 7)⁻¹ = ((4 : ℕ) : ZMod 7)
    apply ZMod.inv_eq_of_mul_eq_one
    change ((2 : ℕ) : ZMod 7) * ((4 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
    rw [← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff' 8 1 7).2
    norm_num
  rw [h40, h2]
  ring_nf
  have h60 : (60 : ZMod 7) = 4 := by
    change ((60 : ℕ) : ZMod 7) = ((4 : ℕ) : ZMod 7)
    apply (ZMod.natCast_eq_natCast_iff' 60 4 7).2
    norm_num
  rw [h60]

/-- The same profile has zero average exactly when its zero-coordinate value is zero. -/
theorem profileAverage_eq_zero_iff (f : ZMod 5 → ZMod 7) :
    (∑ r : Fin 5, ∑ i : Fin 8, profileValue f r i) / (40 : ZMod 7) = 0 ↔
      f 0 = 0 := by
  rw [profileAverage]
  have h2 : (2 : ZMod 7)⁻¹ = 4 := by
    change ((2 : ℕ) : ZMod 7)⁻¹ = ((4 : ℕ) : ZMod 7)
    apply ZMod.inv_eq_of_mul_eq_one
    change ((2 : ℕ) : ZMod 7) * ((4 : ℕ) : ZMod 7) = ((1 : ℕ) : ZMod 7)
    rw [← Nat.cast_mul]
    apply (ZMod.natCast_eq_natCast_iff' 8 1 7).2
    norm_num
  rw [div_eq_mul_inv, h2]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hzero | hbad
    · exact hzero
    · have hne : (4 : ZMod 7) ≠ 0 := by decide
      exact (hne hbad).elim
  · intro h
    rw [h]
    simp

end MathlibPlus.Combinatorics.ProfileAverage
