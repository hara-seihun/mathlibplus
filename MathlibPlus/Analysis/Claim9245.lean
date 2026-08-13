import Mathlib

open scoped ComplexConjugate

namespace MathlibPlus.Analysis

/-- On a fixed circle, squared distance from one determines the real part. -/
theorem fixed_circle_distance_determines_real_part_claim9245
    {a : ℂ} {R d : ℝ} (ha : ‖a‖ = R) (hd : ‖a - 1‖ ^ 2 = d) :
    d = R ^ 2 + 1 - 2 * a.re := by
  calc
    d = ‖a - 1‖ ^ 2 := hd.symm
    _ = Complex.normSq (a - 1) := Complex.sq_norm (a - 1)
    _ = Complex.normSq a + Complex.normSq 1 - 2 * (a * conj 1).re :=
      Complex.normSq_sub a 1
    _ = R ^ 2 + 1 - 2 * a.re := by
      rw [Complex.normSq_eq_norm_sq, ha]
      simp [Complex.normSq_apply]

/-- A conjugation-stable nonreal fixed-circle shell is one conjugate pair. -/
theorem fixed_circle_shell_is_conjugate_pair_claim9245
    {S : Set ℂ} {R d : ℝ}
    (hS : S.Nonempty)
    (hcircle : ∀ z ∈ S, ‖z‖ = R)
    (hdist : ∀ z ∈ S, ‖z - 1‖ ^ 2 = d)
    (hconj : ∀ z, z ∈ S ↔ conj z ∈ S)
    (hreal : ∀ z ∈ S, z.im ≠ 0) :
    ∃ z, z ∈ S ∧ z.im ≠ 0 ∧ z ≠ conj z ∧ S = {z, conj z} := by
  rcases hS with ⟨z, hz⟩
  have hzneq : z ≠ conj z := by
    intro h
    have him : z.im = 0 := by
      have h' : z.im = -z.im := by
        simpa using congrArg Complex.im h
      linarith
    exact (hreal z hz) him
  refine ⟨z, hz, hreal z hz, hzneq, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    have hRe : y.re = z.re := by
      have hy' := fixed_circle_distance_determines_real_part_claim9245
        (hcircle y hy) (hdist y hy)
      have hz' := fixed_circle_distance_determines_real_part_claim9245
        (hcircle z hz) (hdist z hz)
      linarith
    have hImSq : y.im ^ 2 = z.im ^ 2 := by
      calc
        y.im ^ 2 = ‖y‖ ^ 2 - y.re ^ 2 :=
          (Complex.sq_norm_sub_sq_re y).symm
        _ = ‖z‖ ^ 2 - z.re ^ 2 := by rw [hcircle y hy, hcircle z hz, hRe]
        _ = z.im ^ 2 := Complex.sq_norm_sub_sq_re z
    rcases eq_or_eq_neg_of_sq_eq_sq y.im z.im hImSq with h | h
    · left
      apply Complex.ext <;> simp [hRe, h]
    · right
      apply Complex.ext <;> simp [hRe, h]
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hz
    · exact (hconj z).mp hz

end MathlibPlus.Analysis
