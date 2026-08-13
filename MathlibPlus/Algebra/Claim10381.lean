import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.GroupWithZero.Commute

namespace MathlibPlus.Algebra

/-- Claim 10381 in a division-ring operator model.  `lam` is required to
commute with the nilpotent part `N`, making explicit the scalar-centrality
interface implicit in the source's `λ I + N` notation. -/
theorem claim10381_nilpotent_resonance_inverse
    {R : Type*} [DivisionRing R] (lam N : R) (J : ℕ)
    (hlam : lam ≠ 0) (hcomm : Commute lam N) (hnil : N ^ J = 0) :
    let a : R := -N * lam⁻¹
    let S : R := Finset.sum (Finset.range J) (fun i => a ^ i)
    let L : R := lam + N
    let I : R := lam⁻¹ * S
    L * I = 1 ∧ I * L = 1 := by
  let a : R := -N * lam⁻¹
  let S : R := Finset.sum (Finset.range J) (fun i => a ^ i)
  let L : R := lam + N
  let I : R := lam⁻¹ * S
  have hlaminv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlam
  have hinvlam : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam
  have hlam_a : Commute lam a := by
    dsimp [a]
    exact hcomm.neg_right.mul_right (Commute.refl lam).inv_right₀
  have ha_lam : Commute a lam := hlam_a.symm
  have hJ : J ≠ 0 := by
    intro hJ
    subst J
    simp at hnil
  have ha_pow : a ^ J = 0 := by
    dsimp [a]
    have hNinv : Commute (-N) lam⁻¹ := hcomm.symm.neg_left.inv_right₀
    rw [hNinv.mul_pow]
    have hneg : (-N) ^ J = 0 := by
      rw [neg_pow, hnil, mul_zero]
    rw [hneg, zero_mul]
  have hprod : lam * (-N * lam⁻¹) = -N := by
    calc
      lam * (-N * lam⁻¹) = (lam * (-N)) * lam⁻¹ := by rw [mul_assoc]
      _ = ((-N) * lam) * lam⁻¹ := by rw [hcomm.neg_right.eq]
      _ = (-N) * (lam * lam⁻¹) := by rw [← mul_assoc]
      _ = -N := by rw [hlaminv, mul_one]
  have hL : L = lam * (1 - a) := by
    dsimp [L, a]
    calc
      lam + N = lam - (-N) := by simp [sub_eq_add_neg]
      _ = lam - (lam * (-N * lam⁻¹)) := by rw [hprod]
      _ = lam * (1 - (-N * lam⁻¹)) := by rw [mul_sub, mul_one]
  have hL' : lam + N = lam * (1 - a) := by
    simpa [L] using hL
  have hsumL : (1 - a) * S = 1 := by
    rw [mul_neg_geom_sum, ha_pow, sub_zero]
  have hsumR : S * (1 - a) = 1 := by
    rw [geom_sum_mul_neg, ha_pow, sub_zero]
  have hcomm_inv : Commute lam⁻¹ a := hlam_a.inv_left₀
  have hsub : Commute (1 - a) lam⁻¹ :=
      (Commute.one_left lam⁻¹).sub_left hcomm_inv.symm
  have hS_lam : Commute S lam := by
    dsimp [S]
    apply Commute.sum_left
    intro i hi
    exact ha_lam.pow_left i
  constructor
  · change (lam + N) * (lam⁻¹ * S) = 1
    rw [hL']
    calc
      (lam * (1 - a)) * (lam⁻¹ * S) = lam * ((1 - a) * lam⁻¹) * S := by simp [mul_assoc]
      _ = lam * (lam⁻¹ * (1 - a)) * S := by
        rw [hsub.eq]
      _ = (lam * lam⁻¹) * ((1 - a) * S) := by simp [mul_assoc]
      _ = 1 := by rw [hlaminv, one_mul, hsumL]
  · change (lam⁻¹ * S) * (lam + N) = 1
    rw [hL']
    calc
      (lam⁻¹ * S) * (lam * (1 - a)) = lam⁻¹ * (S * lam) * (1 - a) := by simp [mul_assoc]
      _ = lam⁻¹ * (lam * S) * (1 - a) := by rw [hS_lam.eq]
      _ = (lam⁻¹ * lam) * (S * (1 - a)) := by simp [mul_assoc]
      _ = 1 := by rw [hinvlam, one_mul, hsumR]

end MathlibPlus.Algebra
