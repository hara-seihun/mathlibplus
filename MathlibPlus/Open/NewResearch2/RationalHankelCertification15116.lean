import MathlibPlus.Open.NewResearch2.RationalHankel15104_15107

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.RationalHankelCertification15116

noncomputable section

open MathlibPlus.Open.NewResearch2.RationalHankelStructure

/-- The Euclidean norm on a finite complex vector. -/
def euclideanNorm {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- Singular values of a finite complex matrix, with the zero-based index of
Mathlib's finite-support singular-value sequence. -/
noncomputable def singularValue {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n ℂ) (k : ℕ) : ℝ :=
  (Matrix.toEuclideanLin M).singularValues k

/-- The exact rational pole-head coefficient sequence `c_n = C A^n b`. -/
def realizedCoefficient {d r : ℕ}
    (C : Matrix (Fin d) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (b : Fin r → ℂ)
    (n : ℕ) : Fin d → ℂ :=
  (C * A ^ n).mulVec b

/-- The finite observability block. -/
def observabilityBlock {d r L : ℕ}
    (C : Matrix (Fin d) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin L × Fin d) (Fin r) ℂ :=
  fun i k => (C * A ^ i.1.val) i.2 k

/-- The finite controllability block. -/
def controllabilityBlock {r K : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) (b : Fin r → ℂ) :
    Matrix (Fin r) (Fin K) ℂ :=
  fun k j => (A ^ j.val).mulVec b k

/-- A Hankel window for the realized sequence, beginning at `n₀`. -/
def realizedHankel {d r L K : ℕ}
    (C : Matrix (Fin d) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (b : Fin r → ℂ)
    (n₀ : ℕ) : Matrix (Fin L × Fin d) (Fin K) ℂ :=
  blockHankel (fun n => realizedCoefficient C A b (n₀ + n)) 0

/-- The finite state index for a Jordan form with multiplicities `m`. -/
abbrev StateIndex (J : ℕ) (m : Fin J → ℕ) :=
  Σ j : Fin J, Fin (m j)

/-- The Jordan matrix with the chain convention used by the admitted
confluent exponential-polynomial representation. -/
def jordanMatrix {J : ℕ} (m : Fin J → ℕ) (lam : Fin J → ℂ) :
    Matrix (StateIndex J m) (StateIndex J m) ℂ := by
  classical
  exact fun x y =>
    if x = y then lam x.1
    else if x.1 = y.1 ∧ x.2.val = y.2.val + 1 then 1 else 0

/-- The normalized confluent Vandermonde matrix, with the exact binomial-power
entries of the Hermite evaluation carrier. -/
def confluentVandermonde {J r : ℕ}
    (m : Fin J → ℕ) (lam : Fin J → ℂ) :
    Matrix (StateIndex J m) (Fin r) ℂ :=
  fun x n =>
    if x.2.val ≤ n.val then
      (Nat.choose n.val x.2.val : ℂ) *
        lam x.1 ^ (n.val - x.2.val)
    else 0

/-- The rectangular confluent Vandermonde window used by an observability
block with `L` time rows. -/
def confluentVandermondeWindow {J L : ℕ}
    (m : Fin J → ℕ) (lam : Fin J → ℂ) :
    Matrix (StateIndex J m) (Fin L) ℂ :=
  fun x n =>
    if x.2.val ≤ n.val then
      (Nat.choose n.val x.2.val : ℂ) *
        lam x.1 ^ (n.val - x.2.val)
    else 0

/-- Observability written in Jordan coordinates. -/
def jordanObservability {d J L : ℕ}
    (m : Fin J → ℕ) (lam : Fin J → ℂ)
    (Cj : Matrix (Fin d) (StateIndex J m) ℂ) :
    Matrix (Fin L × Fin d) (StateIndex J m) ℂ :=
  fun i x =>
    (Cj * jordanMatrix m lam ^ i.1.val) i.2 x

/-- The residue/output chain factor multiplying each confluent Vandermonde
column in a Jordan-coordinate observability block. -/
def jordanOutputMix {d J : ℕ}
    (m : Fin J → ℕ)
    (Cj : Matrix (Fin d) (StateIndex J m) ℂ)
    (ell : Fin d) :
    Matrix (StateIndex J m) (StateIndex J m) ℂ := by
  classical
  exact fun q x =>
    if h : q.1 = x.1 ∧ x.2.val + q.2.val < m x.1 then
      Cj ell ⟨x.1, ⟨x.2.val + q.2.val, h.2⟩⟩
    else 0

/-- The exact Jordan-coordinate factorization of observability entries. -/
def jordanObservabilityFactorization {d J L : ℕ}
    (m : Fin J → ℕ) (lam : Fin J → ℂ)
    (Cj : Matrix (Fin d) (StateIndex J m) ℂ) : Prop :=
  ∀ (i : Fin L) (ell : Fin d) (x : StateIndex J m),
    jordanObservability m lam Cj (i, ell) x =
      ∑ q : StateIndex J m,
        confluentVandermondeWindow m lam q i *
          jordanOutputMix m Cj ell q x

/-- The top-chain output jet at a Jordan node, expressed without selecting a
noncanonical proof-bearing index. -/
def hasWeakHighestOutputJets {d J : ℕ}
    (m : Fin J → ℕ)
    (Cj : Matrix (Fin d) (StateIndex J m) ℂ)
    (τ : ℝ) : Prop :=
  ∀ j : Fin J, ∃ s : Fin (m j),
    s.val + 1 = m j ∧
      euclideanNorm (fun i : Fin d => Cj i ⟨j, s⟩) ≤ τ

/-- Clustering of distinct nodes can make the confluent Vandermonde factor
arbitrarily ill-conditioned. -/
def nodeClusteringDegradesVandermonde {J : ℕ}
    (m : Fin J → ℕ) : Prop :=
  2 ≤ J →
    ∀ δ : ℝ, 0 < δ →
      ∃ lam' : Fin J → ℂ,
        (∀ j, 0 < m j) ∧
        (∀ j k, j ≠ k → lam' j ≠ lam' k) ∧
        (∃ j k, j ≠ k ∧ ‖lam' j - lam' k‖ < δ) ∧
        singularValue
            (confluentVandermonde
              (r := Fintype.card (StateIndex J m)) m lam')
          (Fintype.card (StateIndex J m) - 1) < δ

/-- With a full-rank Jordan-coordinate observability block, scaling the
highest output/residue jets down produces arbitrarily small observability
singular values while preserving full rank. -/
def weakHighestJetsDegradeObservability {d J L : ℕ}
    (m : Fin J → ℕ) (lam : Fin J → ℂ)
    (Cj : Matrix (Fin d) (StateIndex J m) ℂ) : Prop :=
  Matrix.rank (jordanObservability (L := L) m lam Cj) =
      Fintype.card (StateIndex J m) →
    ∀ δ : ℝ, 0 < δ →
      ∃ t : ℝ, 0 < t ∧
        Matrix.rank
            (jordanObservability (L := L) m lam ((t : ℂ) • Cj)) =
          Fintype.card (StateIndex J m) ∧
        hasWeakHighestOutputJets m ((t : ℂ) • Cj) δ ∧
        singularValue
            (jordanObservability (L := L) m lam ((t : ℂ) • Cj))
          (Fintype.card (StateIndex J m) - 1) < δ

/-- Explicit rational rank-conditioning lower bound.  The final Jordan clause
retains both conditioning mechanisms named in the admitted assertion: the
confluent Vandermonde factor for clustered nodes and the observability factor
for weak highest residue/output jets. -/
def claim_15116 : Prop :=
  ∀ (d r L K n₀ : ℕ)
    (C : Matrix (Fin d) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (b : Fin r → ℂ),
    0 < r → r ≤ L → r ≤ K →
    let O := observabilityBlock (L := L) C A
    let Kmat := controllabilityBlock (K := K) A b
    let H₀ := realizedHankel (L := L) (K := K) C A b n₀
    Matrix.rank O = r →
    Matrix.rank Kmat = r →
    H₀ = O * A ^ n₀ * Kmat ∧
      singularValue H₀ (r - 1) ≥
        singularValue O (r - 1) *
          singularValue (A ^ n₀ * Kmat) (r - 1) ∧
      ∃ (J : ℕ) (m : Fin J → ℕ) (lam : Fin J → ℂ)
        (V : Matrix (Fin r) (StateIndex J m) ℂ)
        (Vinv : Matrix (StateIndex J m) (Fin r) ℂ),
        (∀ j, 0 < m j) ∧
        (∀ j k, j ≠ k → lam j ≠ lam k) ∧
        (∑ j : Fin J, m j) = r ∧
        V * Vinv = 1 ∧ Vinv * V = 1 ∧
        A = V * jordanMatrix m lam * Vinv ∧
        let Cj := C * V
        Matrix.rank (jordanObservability (L := L) m lam Cj) =
            Fintype.card (StateIndex J m) ∧
          jordanObservabilityFactorization (L := L) m lam Cj ∧
          nodeClusteringDegradesVandermonde m ∧
          weakHighestJetsDegradeObservability (L := L) m lam Cj

end
end MathlibPlus.Open.NewResearch2.RationalHankelCertification15116
