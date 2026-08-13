import Mathlib

namespace MathlibPlus.Algebra.Claim37790

/-- Four distinct interpolation nodes always admit a polynomial of degree at
most three through arbitrary prescribed values.  This is the exact cubic
interpolant core of the five-row obstruction; the source-specific derivative
and transporter carriers are not silently identified with these nodes. -/
theorem cubic_interpolant_claim37790
    {F : Type*} [Field F] (x y : Fin 4 → F)
    (hx : Function.Injective x) :
    ∃ p : Polynomial F,
      p.natDegree ≤ 3 ∧ ∀ i, p.eval (x i) = y i := by
  let s : Finset (Fin 4) := Finset.univ
  let p : Polynomial F := Lagrange.interpolate s x y
  refine ⟨p, ?_, ?_⟩
  · rw [Polynomial.natDegree_le_iff_degree_le]
    have hdeg := Lagrange.degree_interpolate_le (s := s) y (hx.injOn)
    simpa [p, s] using hdeg
  · intro i
    exact Lagrange.eval_interpolate_at_node (s := s) y hx.injOn (by simp [s])

end MathlibPlus.Algebra.Claim37790
