import Mathlib

/-!
# The Li--Gram kernel

Exact algebraic records extracted from packet `D-0044`.  This module only fixes the
bilateral coefficient convention and its associated difference kernel; it does not
assert the analytic identification with the Riemann hypothesis.
-/

namespace MathlibPlus.NumberTheory.LiGram

/-- A bilateral real sequence with the packet's even Li-coefficient convention:
its central coefficient vanishes and its negative-index coefficients are obtained by
reflection. -/
def IsEvenLiSequence (lambda : ℤ → ℝ) : Prop :=
  lambda 0 = 0 ∧ ∀ n : ℤ, lambda (-n) = lambda n

/-- The Li--Gram difference kernel associated to a bilateral coefficient sequence. -/
def kernel (lambda : ℤ → ℝ) (j k : ℤ) : ℝ :=
  lambda j + lambda k - lambda (j - k)

/-- An even bilateral sequence gives a symmetric Li--Gram kernel. -/
theorem kernel_comm {lambda : ℤ → ℝ} (hlambda : IsEvenLiSequence lambda) (j k : ℤ) :
    kernel lambda j k = kernel lambda k j := by
  have hdiff : lambda (j - k) = lambda (k - j) := by
    rw [← hlambda.2 (j - k)]
    congr 1
    omega
  simp only [kernel]
  rw [hdiff]
  ring

/-- The diagonal of the Li--Gram kernel is twice the corresponding coefficient. -/
theorem kernel_diagonal {lambda : ℤ → ℝ} (hzero : lambda 0 = 0) (n : ℤ) :
    kernel lambda n n = 2 * lambda n := by
  simp [kernel, hzero]
  ring

/-- Consequently, nonnegativity of every diagonal kernel entry is exactly
nonnegativity of every bilateral Li coefficient. -/
theorem kernel_diagonal_nonnegative_iff {lambda : ℤ → ℝ} (hzero : lambda 0 = 0) :
    (∀ n : ℤ, 0 ≤ kernel lambda n n) ↔ ∀ n : ℤ, 0 ≤ lambda n := by
  constructor
  · intro h n
    have hn := h n
    rw [kernel_diagonal hzero n] at hn
    linarith
  · intro h n
    rw [kernel_diagonal hzero n]
    exact mul_nonneg (by norm_num) (h n)

end MathlibPlus.NumberTheory.LiGram
