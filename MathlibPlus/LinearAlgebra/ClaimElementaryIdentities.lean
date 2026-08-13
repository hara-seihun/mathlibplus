import Mathlib

open scoped BigOperators

/-! Exact formalizations of admitted claims 10162 and 53612. -/

namespace MathlibPlus.LinearAlgebra.Claim10162

/-- A diagonal commutator sends a vector in the lower kernel to the diagonal
image of that vector. -/
theorem commutatorOnKernel
    {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (lower raise diagonal : (Fin n → 𝕜) →ₗ[𝕜] (Fin n → 𝕜))
    (hcomm : lower.comp raise - raise.comp lower = diagonal)
    (v : Fin n → 𝕜) (hv : lower v = 0) :
    lower (raise v) = diagonal v := by
  have h := congrArg (fun f : (Fin n → 𝕜) →ₗ[𝕜] (Fin n → 𝕜) => f v) hcomm
  simpa [LinearMap.sub_apply, hv] using h

/-- In a basis in which the commutator is diagonal, a raising operator preserves
`ker lower` exactly on vectors supported in the zero diagonal entries. -/
theorem diagonalCommutatorPreservesKernel
    {𝕜 : Type*} [Field 𝕜] {n : ℕ}
    (lower raise diagonal : (Fin n → 𝕜) →ₗ[𝕜] (Fin n → 𝕜))
    (d : Fin n → 𝕜)
    (hcomm : lower.comp raise - raise.comp lower = diagonal)
    (hdiag : ∀ w i, diagonal w i = d i * w i)
    (v : Fin n → 𝕜) (hv : lower v = 0) :
    lower (raise v) = 0 ↔ ∀ i, v i ≠ 0 → d i = 0 := by
  have hcore : lower (raise v) = diagonal v :=
    commutatorOnKernel lower raise diagonal hcomm v hv
  constructor
  · intro hpres i hvi
    have hi_fun : diagonal v = 0 := by
      rw [← hcore]
      exact hpres
    have hi : diagonal v i = 0 := by
      have := congrFun hi_fun i
      simpa using this
    have hprod : d i * v i = 0 := by
      simpa [hdiag] using hi
    exact (mul_eq_zero.mp hprod).resolve_right hvi
  · intro hsupp
    rw [hcore]
    ext i
    rw [hdiag]
    by_cases hvi : v i = 0
    · simp [hvi]
    · simp [hsupp i hvi]

end MathlibPlus.LinearAlgebra.Claim10162

namespace MathlibPlus.LinearAlgebra.Claim53612

/-- The scalar and vector column sums in the displayed finite telescoping
construction are respectively zero and nonzero. -/
theorem telescopingScalarAndResponse
    (l n : ℕ) (V : ℕ → (Fin n → ℚ)) (b : ℕ → ℚ)
    (hV : V l = V 0) (hb : b 0 ≠ b l) :
    (∑ i ∈ Finset.range l, (V i - V (i + 1))) = 0 ∧
      (∑ i ∈ Finset.range l, (b i - b (i + 1))) ≠ 0 := by
  have htelV : ∀ m, (∑ i ∈ Finset.range m, (V i - V (i + 1))) = V 0 - V m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        abel
  have htelb : ∀ m, (∑ i ∈ Finset.range m, (b i - b (i + 1))) = b 0 - b m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        abel
  constructor
  · rw [htelV, hV]
    simp
  · rw [htelb]
    exact sub_ne_zero.mpr hb

end MathlibPlus.LinearAlgebra.Claim53612
