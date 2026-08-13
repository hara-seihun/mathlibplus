import Mathlib

open scoped ComplexConjugate

namespace MathlibPlus.Algebra.Claim10789

/-- The finite passive inner quartet from claim 10789.  The reciprocal identity
is stated away from the zeros and poles of the rational function; the boundary
and half-plane assertions include their respective nonvanishing consequences. -/
theorem passiveInnerOffAxisQuartet :
    let a : ℂ := 1 + 2 * Complex.I
    let E : ℂ → ℂ := fun z => z ^ 2 + 2 * z + 5
    let Y : ℂ → ℂ := fun z => E z * E (-z)
    let S : ℂ → ℂ := fun z => E (-z) / E z
    (∀ z : ℂ, E z = (z + a) * (z + star a)) ∧
      (∀ z : ℂ, Y z = z ^ 4 + 6 * z ^ 2 + 25) ∧
      (∀ z : ℂ,
        Y z = 0 ↔
          z = (1 : ℂ) + 2 * Complex.I ∨
            z = (1 : ℂ) - 2 * Complex.I ∨
            z = -(1 : ℂ) + 2 * Complex.I ∨
            z = -(1 : ℂ) - 2 * Complex.I) ∧
      (∀ z : ℂ, E z ≠ 0 → E (-z) ≠ 0 → S z * S (-z) = 1) ∧
      (∀ z : ℂ, S (star z) = star (S z)) ∧
      (∀ t : ℝ, ‖S ((t : ℂ) * Complex.I)‖ = 1) ∧
      (∀ z : ℂ, 0 < z.re → ‖S z‖ < 1) := by
  let a : ℂ := 1 + 2 * Complex.I
  let E : ℂ → ℂ := fun z => z ^ 2 + 2 * z + 5
  let Y : ℂ → ℂ := fun z => E z * E (-z)
  let S : ℂ → ℂ := fun z => E (-z) / E z
  change
    (∀ z : ℂ, E z = (z + a) * (z + star a)) ∧
      (∀ z : ℂ, Y z = z ^ 4 + 6 * z ^ 2 + 25) ∧
      (∀ z : ℂ,
        Y z = 0 ↔
          z = (1 : ℂ) + 2 * Complex.I ∨
            z = (1 : ℂ) - 2 * Complex.I ∨
            z = -(1 : ℂ) + 2 * Complex.I ∨
            z = -(1 : ℂ) - 2 * Complex.I) ∧
      (∀ z : ℂ, E z ≠ 0 → E (-z) ≠ 0 → S z * S (-z) = 1) ∧
      (∀ z : ℂ, S (star z) = star (S z)) ∧
      (∀ t : ℝ, ‖S ((t : ℂ) * Complex.I)‖ = 1) ∧
      (∀ z : ℂ, 0 < z.re → ‖S z‖ < 1)
  have hstarA : star a = 1 - 2 * Complex.I := by
    dsimp [a]
    simp [map_add, map_mul, map_ofNat]
    ring
  have hstarA' : (starRingEnd ℂ) a = 1 - 2 * Complex.I := by
    simpa only [starRingEnd_apply] using hstarA
  have hfactor (z : ℂ) : E z = (z + a) * (z + star a) := by
    dsimp [E, a]
    simp [map_add, map_mul, map_ofNat, pow_two]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hEzero (z : ℂ) :
      E z = 0 ↔ z = -(1 : ℂ) - 2 * Complex.I ∨
        z = -(1 : ℂ) + 2 * Complex.I := by
    rw [hfactor]
    dsimp [a]
    simp [map_add, map_mul, map_ofNat, pow_two, Complex.I_sq]
    constructor
    · rintro (h | h)
      · left
        linear_combination h
      · right
        linear_combination h
    · rintro (h | h)
      · left
        linear_combination h
      · right
        linear_combination h
  have hYzero (z : ℂ) :
      Y z = 0 ↔
        z = (1 : ℂ) + 2 * Complex.I ∨
          z = (1 : ℂ) - 2 * Complex.I ∨
          z = -(1 : ℂ) + 2 * Complex.I ∨
          z = -(1 : ℂ) - 2 * Complex.I := by
    dsimp [Y]
    rw [mul_eq_zero, hEzero z, hEzero (-z)]
    constructor
    · intro h
      rcases h with h | h
      · rcases h with h | h
        · right
          right
          right
          exact h
        · right
          right
          left
          exact h
      · rcases h with h | h
        · left
          have h' := congrArg Neg.neg h
          convert h' using 1 <;> ring
        · right
          left
          have h' := congrArg Neg.neg h
          convert h' using 1 <;> ring
    · intro h
      rcases h with h | h | h | h
      · right
        left
        have h' := congrArg Neg.neg h
        convert h' using 1 <;> ring
      · right
        right
        have h' := congrArg Neg.neg h
        convert h' using 1 <;> ring
      · left
        right
        exact h
      · left
        left
        exact h
  have hconjE (z : ℂ) : E (star z) = star (E z) := by
    dsimp [E]
    simp [map_add, map_mul, map_ofNat]
  have hboundary_nonzero (t : ℝ) : E ((t : ℂ) * Complex.I) ≠ 0 := by
    have hnorm :
        Complex.normSq (E ((t : ℂ) * Complex.I)) =
          (5 - t ^ 2) ^ 2 + 4 * t ^ 2 := by
      dsimp [E]
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        pow_two, Complex.I_sq]
      ring
    have hnorm_pos : 0 < Complex.normSq (E ((t : ℂ) * Complex.I)) := by
      rw [hnorm]
      nlinarith [sq_nonneg (t ^ 2 - 3)]
    intro h
    rw [h] at hnorm_pos
    norm_num at hnorm_pos
  refine ⟨hfactor, ?_, hYzero, ?_, ?_, ?_, ?_⟩
  · intro z
    dsimp [Y, E]
    ring
  · intro z hz hneg
    dsimp [S]
    field_simp [hz, hneg]
  · intro z
    dsimp [S]
    simp only [starRingEnd_apply]
    have hnum : E (-(star z)) = star (E (-z)) := by
      simpa using hconjE (-z)
    rw [hnum, hconjE]
    simp
  · intro t
    dsimp [S]
    have hstar_it : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
      simp
    have hboundary :
        E (-((t : ℂ) * Complex.I)) = star (E ((t : ℂ) * Complex.I)) := by
      simpa [hstar_it] using hconjE ((t : ℂ) * Complex.I)
    rw [norm_div, hboundary, norm_star]
    exact div_self (norm_ne_zero_iff.mpr (hboundary_nonzero t))
  · intro z hz
    have hden : E z ≠ 0 := by
      intro h
      rw [hfactor z] at h
      dsimp [a] at h
      simp [map_add, map_mul, map_ofNat] at h
      rcases h with h | h
      · have hr : z.re + 1 = 0 := by
          simpa using congrArg Complex.re h
        linarith
      · have hr : z.re + 1 = 0 := by
          simpa using congrArg Complex.re h
        linarith
    have hdiff :
        Complex.normSq (E z) - Complex.normSq (E (-z)) =
          8 * z.re * (Complex.normSq z + 5) := by
      dsimp [E]
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
      ring
    have hdiff_pos :
        0 < Complex.normSq (E z) - Complex.normSq (E (-z)) := by
      rw [hdiff]
      have hzsq : 0 ≤ Complex.normSq z := by
        rw [Complex.normSq_apply]
        nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      nlinarith
    have hsq : ‖E (-z)‖ ^ 2 < ‖E z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      nlinarith [hdiff_pos]
    have hnorm : ‖E (-z)‖ < ‖E z‖ := by
      nlinarith [hsq, norm_nonneg (E (-z)), norm_nonneg (E z)]
    dsimp [S]
    rw [norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hden)).2
    simpa using hnorm

end MathlibPlus.Algebra.Claim10789
