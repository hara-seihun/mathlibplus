import Mathlib

namespace MathlibPlus.Open.AdmittedBatch

/--
Chebyshev trailing-resolvent tunneling bound.  The matrix is the finite
real-symmetric tridiagonal trailing block on coordinates `k+1, ..., N-1`,
so coordinate `m` has trailing-block coordinate `d = m-k-1`.
-/
def chebyshevTrailingResolventTunnelingBound : Prop :=
  ∀ (N k m : ℕ)
    (H_k : Matrix (Fin (N - k - 1)) (Fin (N - k - 1)) ℝ)
    (A B x : ℝ),
    (hkm : k < m) →
    (hmN : m < N) →
    (∀ i j, H_k i j = H_k j i) →
    (∀ i j,
      i.val + 1 < j.val ∨ j.val + 1 < i.val →
      H_k i j = 0) →
    spectrum ℝ H_k ⊆ Set.Icc A B →
    A < B →
    B < x →
    let d : Fin (N - k - 1) := ⟨m - k - 1, by omega⟩
    let κ := Real.arcosh (1 + 2 * (x - B) / (B - A))
    |dotProduct
        (Pi.single d (1 : ℝ))
        (Matrix.mulVec
          ((x • (1 : Matrix (Fin (N - k - 1)) (Fin (N - k - 1)) ℝ) - H_k)⁻¹)
          (Pi.single (⟨0, by omega⟩ : Fin (N - k - 1)) (1 : ℝ)))| ≤
      2 * Real.exp (-((d : ℕ) : ℝ) * κ) /
        (Real.sqrt ((x - A) * (x - B)) * (1 - Real.exp (-κ)))

end MathlibPlus.Open.AdmittedBatch
