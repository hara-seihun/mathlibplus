import Mathlib

open scoped BigOperators ComplexConjugate

namespace MathlibPlus.Analysis.FiniteWeilPositivity

private lemma critical_reflection_eq (z : ℂ)
    (hz : z.re = (1 : ℝ) / 2) :
    1 - conj z = z := by
  apply Complex.ext
  · norm_num [Complex.sub_re, hz]
  · simp [Complex.sub_im]

/-- A finite Weil form on a packet supported on the critical line is
nonnegative on every represented transform. -/
theorem criticalLineSupport_finiteWeil_nonnegative_claim4873
    {n : ℕ} (roots : Fin n → ℂ) (F : ℂ → ℂ)
    (hroots : ∀ i, (roots i).re = (1 : ℝ) / 2) :
    0 ≤ ∑ i, ((F (roots i) * conj (F (1 - conj (roots i)))).re) := by
  have hreflect : ∀ i, 1 - conj (roots i) = roots i :=
    fun i => critical_reflection_eq (roots i) (hroots i)
  simp_rw [hreflect]
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.mul_conj]
  exact Complex.normSq_nonneg _

end MathlibPlus.Analysis.FiniteWeilPositivity
