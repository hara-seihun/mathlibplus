import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable section

def terminalIndex {N : ℕ} (hN : 0 < N) : Fin N :=
  Fin.cast (Nat.sub_add_cancel (Nat.succ_le_of_lt hN)) (Fin.last (N - 1))

def reverseIndex {N : ℕ} (hN : 0 < N) (r : ℕ) (hr : r < N) : Fin N :=
  ⟨N - (r + 1), Nat.sub_lt hN (Nat.succ_pos r)⟩

def reverseEndpointValue {N : ℕ} (hN : 0 < N)
    (v : Fin N → ℝ) (r : ℕ) : ℝ :=
  if hr : r < N then
    v (reverseIndex hN r hr) / v (terminalIndex hN)
  else
    0

def reverseKernel {N : ℕ} (hN : 0 < N)
    (v : Fin N → ℝ) (m : ℕ) : ℝ :=
  ∑ r : Fin (m + 1), reverseEndpointValue hN v r.val ^ 2

def trailingIndex {N d : ℕ} (hd : d ≤ N) (r : Fin d) : Fin N :=
  Fin.cast (Nat.sub_add_cancel hd) (Fin.natAdd (N - d) r)

def trailingPrincipalBlock {N d : ℕ} (hd : d ≤ N)
    (J : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  J.submatrix (trailingIndex hd) (trailingIndex hd)

def lambdaMax {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {z : ℝ | ∃ u : Fin n → ℝ, u ≠ 0 ∧ H.mulVec u = z • u}

def irreducibleRealJacobi {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, J i j = J j i) ∧
    (∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → J i j = 0) ∧
      (∀ i j, i.val + 1 = j.val → 0 < J i j)

def normalizedSpectralData {N : ℕ}
    (J : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin N → ℝ) (v : Fin N → Fin N → ℝ) : Prop :=
  (∀ i, ∑ a, v i a ^ 2 = 1) ∧
    (∀ i j, ∑ a, v i a * v j a = if i = j then 1 else 0) ∧
      (∀ a b, J a b = ∑ i, x i * v i a * v i b)

def trailingBlockUpperSpectralEdge_8753 : Prop :=
  ∀ (N d : ℕ) (hN : 0 < N) (hd : 0 < d ∧ d ≤ N)
    (J : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin N → ℝ) (v : Fin N → Fin N → ℝ) (B : ℝ),
    irreducibleRealJacobi J →
      normalizedSpectralData J x v →
        lambdaMax (trailingPrincipalBlock hd.2 J) ≤
          B +
            ∑ i ∈ Finset.univ.filter (fun i => B < x i),
              (x i - B) *
                (reverseKernel hN (v i) (d - 1) /
                  reverseKernel hN (v i) (N - 1))

end

end MathlibPlus.Open.Analysis
