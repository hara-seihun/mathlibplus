import Mathlib.Data.Rat.Cast.Order
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibPlus.Algebra.Claim22802
open Polynomial

/-- The displayed nonmonic unit-resultant family from claim 22802. -/
theorem unitResultantNonmonicFamily_22802 (m : ℤ) (_hm : (-1 : ℤ) ≤ m) :
    let ell : ℤ[X] := X ^ 3 - C (2 * m + 4) * X ^ 2 + C m * X + C 1
    let d : ℤ[X] := C 2 * X - C 1
    ell.resultant d 3 1 = -1 ∧ d.natDegree = 1 ∧ d.leadingCoeff = 2 := by
  dsimp
  let ι : ℤ →+* ℚ := Int.castRingHom ℚ
  let ell : ℤ[X] := X ^ 3 - C (2 * m + 4) * X ^ 2 + C m * X + C 1
  let d : ℤ[X] := C 2 * X - C 1
  let f : ℚ[X] := Polynomial.map ι ell
  let g : ℚ[X] := Polynomial.map ι d
  have hg : g = Polynomial.C (2 : ℚ) * (X - Polynomial.C (1 / 2 : ℚ)) := by
    ext k
    simp [g, d, ι, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_C,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    by_cases hk0 : k = 0
    · simp [hk0]
    by_cases hk1 : k = 1
    · simp [hk0, hk1]
    · simp [hk0, hk1]
  have heqell : ell = C (1 : ℤ) * X ^ 3 + C (-(2 * m + 4)) * X ^ 2 +
      C m * X + C 1 := by
    simp [ell, sub_eq_add_neg]
    ring
  have helldeg : ell.natDegree ≤ 3 := by
    rw [heqell]
    exact Polynomial.natDegree_cubic_le
  have hfdeg : f.natDegree ≤ 3 :=
    (Polynomial.natDegree_map_le).trans helldeg
  have heval : Polynomial.eval (1 / 2 : ℚ) f = 1 / 8 := by
    simp [f, ell, ι, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow]
    ring
  have hresQ : f.resultant g 3 1 = (-1 : ℚ) := by
    rw [hg, Polynomial.resultant_C_mul_right, Polynomial.resultant_X_sub_C_right f 3
      (1 / 2 : ℚ) hfdeg, heval]
    norm_num
  have hmap := Polynomial.resultant_map_map ell d 3 1 ι
  have hcast : (ι (ell.resultant d 3 1)) = (-1 : ℚ) := by
    rw [← hmap]
    simpa [f, g] using hresQ
  have hres : ell.resultant d 3 1 = (-1 : ℤ) := by
    apply Int.cast_injective (α := ℚ)
    simpa [ι] using hcast
  have hdcoeff : d.coeff 1 = 2 := by
    simp [d, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul,
      Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_C]
  have heqd : d = C 2 * X + C (-1 : ℤ) := by
    simp [d, sub_eq_add_neg]
  have hddeg_le : d.natDegree ≤ 1 := by
    rw [heqd]
    exact Polynomial.natDegree_linear_le
  have hddeg : d.natDegree = 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hddeg_le
    rw [hdcoeff]
    norm_num
  have hdlead : d.leadingCoeff = 2 := by
    rw [Polynomial.leadingCoeff, hddeg]
    exact hdcoeff
  exact ⟨hres, hddeg, hdlead⟩

end MathlibPlus.Algebra.Claim22802
