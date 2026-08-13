import MathlibPlus.Algebra.WeightedEulerIdentity

namespace MathlibPlus.Algebra

open scoped BigOperators
open MvPolynomial

/-- For a fixed nonzero weighted degree, the first partials determine a
weighted-homogeneous rational polynomial.  This is the row-equality consequence
of weighted Euler reconstruction. -/
theorem weightedEuler_firstPartials_eq_iff_claim52164
    {n : ℕ} (w : Fin n → ℕ) (d : ℕ)
    (p q : MvPolynomial (Fin n) ℚ)
    (hp : ∀ m ∈ p.support, ∑ i : Fin n, w i * m i = d)
    (hq : ∀ m ∈ q.support, ∑ i : Fin n, w i * m i = d)
    (hd : (d : ℚ) ≠ 0) :
    (∀ i : Fin n, pderiv i p = pderiv i q) ↔ p = q := by
  constructor
  · intro h
    rw [weightedEulerReconstruction w d p hd hp,
      weightedEulerReconstruction w d q hd hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i]
  · intro h i
    rw [h]

end MathlibPlus.Algebra
