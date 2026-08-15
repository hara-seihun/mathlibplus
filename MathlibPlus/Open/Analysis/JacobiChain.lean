import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

/-- The zero-diagonal Jacobi matrix specified by the edge coefficients. -/
def jacobiMatrix (N : ℕ) (a : Fin (N + 1) → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i k =>
    if i.1 = k.1 + 1 then
      a (Fin.castSucc i)
    else if k.1 = i.1 + 1 then
      a (Fin.castSucc k)
    else
      0

/-- The coordinate formula for the Jacobi action, with zero boundary values. -/
def jacobiAction (N : ℕ) (a : Fin (N + 1) → ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  fun j =>
    (if h : 0 < j.1 then
      a ⟨j.1, by omega⟩ * v ⟨j.1 - 1, by omega⟩
    else
      0) +
    (if h : j.1 + 1 < N then
      a ⟨j.1 + 1, by omega⟩ * v ⟨j.1 + 1, h⟩
    else
      0)

/-- Claim 8797: a positive zero-diagonal finite Jacobi eigenpair. -/
def positiveZeroDiagonalFiniteJacobiChain
    (N : ℕ) (a : Fin (N + 1) → ℝ) (v : Fin N → ℝ)
    (lam : ℝ) (𝒜 : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  a 0 = 0 ∧
  a ⟨N, by omega⟩ = 0 ∧
  (∀ q : Fin (N + 1), 1 ≤ q.1 → q.1 < N → 0 < a q) ∧
  0 < lam ∧
  𝒜 = jacobiMatrix N a ∧
  (∀ j : Fin N, (𝒜.mulVec v) j = jacobiAction N a v j) ∧
  𝒜.mulVec v = lam • v

/-- The embedding of suffix coordinates `0,...,N-j-1` into `j,...,N-1`. -/
def suffixIndex (N j : ℕ) (hj : j < N) (p : Fin (N - j)) : Fin N :=
  ⟨j + p.1, by omega⟩

/-- The trailing Jacobi block on global coordinates `j,...,N-1`. -/
def suffixBlock (N : ℕ) (a : Fin (N + 1) → ℝ) (j : ℕ) (hj : j < N) :
    Matrix (Fin (N - j)) (Fin (N - j)) ℝ :=
  (jacobiMatrix N a).submatrix (suffixIndex N j hj) (suffixIndex N j hj)

/-- The eigenvector restricted and reindexed to a suffix. -/
def suffixVector (N : ℕ) (v : Fin N → ℝ) (j : ℕ) (hj : j < N) : Fin (N - j) → ℝ :=
  fun p => v (suffixIndex N j hj p)

/-- The maximum of `a_k,...,a_(N-1)` for `k<N`. -/
def futureEdgeMaximum (N : ℕ) (a : Fin (N + 1) → ℝ) (k : Fin N) : ℝ :=
  let s := Finset.univ.filter (fun ℓ : Fin (N + 1) => k.1 ≤ ℓ.1 ∧ ℓ.1 < N)
  s.sup'
    (by
      refine ⟨Fin.castSucc k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, k.isLt⟩⟩)
    (fun ℓ => a ℓ)

/-- The edge envelope, with the stipulated value `A_N=0`. -/
def edgeEnvelope (N : ℕ) (a : Fin (N + 1) → ℝ) (k : Fin (N + 1)) : ℝ :=
  if hk : k.1 < N then
    futureEdgeMaximum N a ⟨k.1, hk⟩
  else
    0

/-- Claim 8798: the suffix block and the future edge envelope. -/
def suffixBlockAndFutureEdgeEnvelope
    (N : ℕ) (a : Fin (N + 1) → ℝ) (j : ℕ)
    (H : Matrix (Fin (N - j)) (Fin (N - j)) ℝ)
    (A : Fin (N + 1) → ℝ) : Prop :=
  ∀ (h₁ : 1 ≤ j) (hj : j < N),
    H = suffixBlock N a j hj ∧
    A ⟨j + 1, by omega⟩ = edgeEnvelope N a ⟨j + 1, by omega⟩ ∧
    A ⟨N, by omega⟩ = 0

/-- The first basis vector of a nonempty finite coordinate space. -/
def endpointVector (m : ℕ) (_hm : 0 < m) : Fin m → ℝ :=
  fun i => if i.1 = 0 then 1 else 0

/-- The endpoint matrix coefficient `⟨e₀,R e₀⟩`. -/
def endpointPairing {m : ℕ} (hm : 0 < m) (R : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∑ i, endpointVector m hm i * (R.mulVec (endpointVector m hm)) i

/-- A two-sided matrix inverse, used to state resolvent existence without a
matrix inverse convention outside the invertible case. -/
def isTwoSidedInverse {m : ℕ} (M R : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  M * R = 1 ∧ R * M = 1

/-- Claim 8799: suffix restriction and the Schur-resolvent ratio identity. -/
def exactSuffixSchurResolventIdentity
    (N : ℕ) (a : Fin (N + 1) → ℝ) (v : Fin N → ℝ) (lam : ℝ)
    (𝒜 : Matrix (Fin N) (Fin N) ℝ) (j : ℕ)
    (H : Matrix (Fin (N - j)) (Fin (N - j)) ℝ) : Prop :=
  ∀ (h₁ : 1 ≤ j) (hj : j < N),
    a 0 = 0 →
    a ⟨N, by omega⟩ = 0 →
    (∀ q : Fin (N + 1), 1 ≤ q.1 → q.1 < N → 0 < a q) →
    0 < lam →
    𝒜 = jacobiMatrix N a →
    (∀ i : Fin N, (𝒜.mulVec v) i = jacobiAction N a v i) →
    𝒜.mulVec v = lam • v →
    H = suffixBlock N a j hj →
    ((lam • (1 : Matrix (Fin (N - j)) (Fin (N - j)) ℝ) - H).mulVec
        (suffixVector N v j hj) =
      (a ⟨j, by omega⟩ * v ⟨j - 1, by omega⟩) • endpointVector (N - j) (by omega) ∧
    (∀ R : Matrix (Fin (N - j)) (Fin (N - j)) ℝ,
      isTwoSidedInverse
          (lam • (1 : Matrix (Fin (N - j)) (Fin (N - j)) ℝ) - H) R →
      v ⟨j, by omega⟩ / v ⟨j - 1, by omega⟩ =
        a ⟨j, by omega⟩ * endpointPairing (by omega) R))

/-- Claim 8800: the positive even-return Neumann expansion. -/
def positiveEvenReturnNeumannExpansion
    (N : ℕ) (a : Fin (N + 1) → ℝ) (lam : ℝ) (j : ℕ)
    (H : Matrix (Fin (N - j)) (Fin (N - j)) ℝ)
    (A : Fin (N + 1) → ℝ) : Prop :=
  ∀ (h₁ : 1 ≤ j) (hj : j < N),
    a 0 = 0 →
    a ⟨N, by omega⟩ = 0 →
    (∀ q : Fin (N + 1), 1 ≤ q.1 → q.1 < N → 0 < a q) →
    H = suffixBlock N a j hj →
    A ⟨j + 1, by omega⟩ = edgeEnvelope N a ⟨j + 1, by omega⟩ →
    A ⟨N, by omega⟩ = 0 →
    0 < lam →
    lam > 2 * A ⟨j + 1, by omega⟩ →
    ∃ R : Matrix (Fin (N - j)) (Fin (N - j)) ℝ,
      isTwoSidedInverse
          (lam • (1 : Matrix (Fin (N - j)) (Fin (N - j)) ℝ) - H) R ∧
      endpointPairing (by omega) R =
        lam⁻¹ * ∑' r : ℕ,
          ((H ^ (2 * r)) ⟨0, by omega⟩ ⟨0, by omega⟩) / lam ^ (2 * r) ∧
      (∀ r : ℕ,
        (H ^ (2 * r + 1)) ⟨0, by omega⟩ ⟨0, by omega⟩ = 0) ∧
      (∀ r : ℕ,
        0 ≤ ((H ^ (2 * r)) ⟨0, by omega⟩ ⟨0, by omega⟩) / lam ^ (2 * r))

end MathlibPlus.Open.Analysis
