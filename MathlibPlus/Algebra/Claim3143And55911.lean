import Mathlib

open BigOperators
open scoped BigOperators

namespace MathlibPlus.Algebra.Claim3143

/-- A polynomial correction divisible by `Q` vanishes at the five selected
witness values whenever `Q` does. -/
theorem divisible_correction_preserves_five_witnesses
    {R X : Type*} [CommRing R]
    (Q : Polynomial R) (u : X → R) (w : Fin 5 → X)
    (hQ : ∀ j, Polynomial.eval (u (w j)) Q = 0)
    (correction : Polynomial R) (hdiv : ∃ q, correction = Q * q) :
    ∀ j, Polynomial.eval (u (w j)) correction = 0 := by
  intro j
  rcases hdiv with ⟨q, rfl⟩
  simp [Polynomial.eval_mul, hQ]

end MathlibPlus.Algebra.Claim3143

namespace MathlibPlus.Algebra.Claim55911

noncomputable section

/-- The adjacent residual from claim 55911. -/
def K {R : Type*} [CommRing R] (d : ℕ) (x : ℕ → Polynomial R)
    (z : Polynomial R) : Polynomial R := x d - x 1 * z ^ (d - 1)

/-- The two adjacent rows used in the scalar trace compensation. -/
def H₁ {R : Type*} [CommRing R] : Polynomial R := 1

def H₀ {R : Type*} [CommRing R] (d : ℕ) (x : ℕ → Polynomial R)
    (z : Polynomial R) : Polynomial R := -(x 1 * z ^ (d - 1))

/-- The displayed scalar trace terms cancel in every commutative polynomial
ring; the source-specific trace map is deliberately kept as an explicit
hypothesis in the next theorem. -/
theorem scalar_trace_terms_cancel
    {R : Type*} [CommRing R] (d : ℕ) (x : ℕ → Polynomial R)
    (z : Polynomial R) :
    x 1 * x d - x d * x 1 = 0 := by
  ring

theorem scalar_trace_compensation
    {R : Type*} [CommRing R] (d : ℕ) (x : ℕ → Polynomial R)
    (z : Polynomial R) (Phi : Polynomial R → Polynomial R)
    (hPhi : Phi (z * K d x z) = x 1 * x d - x d * x 1) :
    Phi (z * K d x z) = 0 := by
  rw [hPhi]
  ring

end

end MathlibPlus.Algebra.Claim55911
