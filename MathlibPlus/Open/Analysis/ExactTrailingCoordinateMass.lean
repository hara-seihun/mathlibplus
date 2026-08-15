import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

noncomputable section

private def basisVector {N : ℕ} (k : Fin N) : EuclideanSpace ℝ (Fin N) :=
  EuclideanSpace.single k 1

private def endpointIndex {N : ℕ} (hN : 0 < N) (r : ℕ) (hr : r < N) : Fin N :=
  ⟨N - 1 - r, by omega⟩

private def trailingProjection {N d : ℕ} (hd : d ≤ N)
    (v : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  ∑ k : Fin N, EuclideanSpace.single k
    (if N - d ≤ (k : ℕ) then inner ℝ (basisVector k) v else 0)

private def terminalWeight {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N)) : ℝ :=
  |inner ℝ (basisVector (endpointIndex hN 0 (by omega))) v| ^ 2

private def reversedEndpointPolynomial {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N)) (r : ℕ) (hr : r < N) : ℝ :=
  inner ℝ (basisVector (endpointIndex hN r hr)) v /
    inner ℝ (basisVector (endpointIndex hN 0 (by omega))) v

private def reversedKernel {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N)) (m : ℕ) (hm : m < N) : ℝ :=
  ∑ r : Fin (m + 1), reversedEndpointPolynomial hN v r.1 (by omega) ^ 2

private def IsIrreducibleJacobi {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ j k, A j k = A k j) ∧
    (∀ j k, j.1 + 1 < k.1 ∨ k.1 + 1 < j.1 → A j k = 0) ∧
    (∀ k : Fin (N - 1),
      0 < A ⟨k.1, by omega⟩ ⟨k.1 + 1, by omega⟩)

def exactTrailingCoordinateMass : Prop :=
  ∀ (N d : ℕ) (hN : 0 < N) (hd : 0 < d ∧ d ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ)
    (v : EuclideanSpace ℝ (Fin N)) (x : ℝ),
    IsIrreducibleJacobi A →
    A.mulVec v = x • v →
    ‖v‖ = 1 →
    ‖trailingProjection hd.2 v‖ ^ 2 =
      terminalWeight hN v * reversedKernel hN v (d - 1) (by omega) ∧
      terminalWeight hN v * reversedKernel hN v (d - 1) (by omega) =
        reversedKernel hN v (d - 1) (by omega) /
          reversedKernel hN v (N - 1) (by omega)

end

end MathlibPlus.Open
