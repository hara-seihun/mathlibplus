import Mathlib

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace MathlibPlus.Open.NewResearch2.R0019

/-- Claim 17236: the Li--Gram kernel is a cumulative Toeplitz congruence. -/
def claim17236 : Prop :=
  ∀ (N : ℕ) (a : ℤ → ℂ),
    let C : Matrix (Fin N) (Fin N) ℂ :=
      fun r s => if s ≤ r then 1 else 0
    let T : Matrix (Fin N) (Fin N) ℂ :=
      fun r s => a ((r.val : ℤ) - (s.val : ℤ))
    let K : Matrix (Fin N) (Fin N) ℂ :=
      fun j k =>
        ∑ r : Fin N, ∑ s : Fin N,
          if r ≤ j ∧ s ≤ k then a ((r.val : ℤ) - (s.val : ℤ)) else 0
    K = C * T * C.conjTranspose ∧
      (∀ j k : Fin N,
        K j k =
          ∑ r : Fin N, ∑ s : Fin N,
            if r ≤ j ∧ s ≤ k then a ((r.val : ℤ) - (s.val : ℤ)) else 0)

/-- Claim 17239: an invertible Hermitian congruence preserves all inertia signs. -/
def claim17239 : Prop :=
  ∀ (N : ℕ) (T C K : Matrix (Fin N) (Fin N) ℂ),
    Matrix.IsHermitian T →
    K = C * T * C.conjTranspose →
    Function.Bijective (C.conjTranspose *ᵥ ·) →
    (∀ v : Fin N → ℂ,
      let w : Fin N → ℂ := C.conjTranspose *ᵥ v
      let qK : ℂ := ∑ i : Fin N, star (v i) * (K *ᵥ v) i
      qK = ∑ i : Fin N, star (w i) * (T *ᵥ w) i ∧
        ((0 : ℝ) < qK.re ↔
          (0 : ℝ) < (∑ i : Fin N, star (w i) * (T *ᵥ w) i).re) ∧
        ((qK.re < 0) ↔
          (∑ i : Fin N, star (w i) * (T *ᵥ w) i).re < 0) ∧
        (qK.re = 0 ↔
          (∑ i : Fin N, star (w i) * (T *ᵥ w) i).re = 0))

end MathlibPlus.Open.NewResearch2.R0019
