import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Finite support for a sequence on the natural ranks. -/
def finiteSupport16737 (a : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n, N < n → a n = 0

/-- Coefficientwise nonnegativity. -/
def nonnegativeSequence16737 (a : ℕ → ℝ) : Prop :=
  ∀ n, 0 ≤ a n

/-- No internal zeros between two nonzero ranks. -/
def noInternalZeros16737 (a : ℕ → ℝ) : Prop :=
  ∀ i j k : ℕ, i ≤ j → j ≤ k →
    a i ≠ 0 → a k ≠ 0 → a j ≠ 0

/-- The adjacent log-concavity inequalities. -/
def adjacentLogConcave16737 (a : ℕ → ℝ) : Prop :=
  ∀ n, 0 < n → a n ^ 2 ≥ a (n - 1) * a (n + 1)

/-- The finite nonnegative log-concave, no-internal-zero sequence class. -/
def logConcaveSequence16737 (a : ℕ → ℝ) : Prop :=
  finiteSupport16737 a ∧
    nonnegativeSequence16737 a ∧
    noInternalZeros16737 a ∧
    adjacentLogConcave16737 a

/-- Unimodality on all natural ranks, including the zero tail. -/
def unimodalSequence16737 (a : ℕ → ℝ) : Prop :=
  ∃ m : ℕ,
    (∀ i j, i ≤ j → j ≤ m → a i ≤ a j) ∧
      (∀ i j, m ≤ i → i ≤ j → a j ≤ a i)

/-- The coefficient convolution of two sequences. -/
def convolution16737 (a b : ℕ → ℝ) : ℕ → ℝ :=
  fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- An entry of the one-sided Toeplitz matrix of a sequence. -/
def toeplitzEntry16737 (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i ≤ j then a (j - i) else 0

/-- TP2 includes the nonnegative 1-by-1 minors and all nonnegative 2-by-2
minors of the Toeplitz matrix. -/
def toeplitzTP2_16737 (a : ℕ → ℝ) : Prop :=
  (∀ i j, 0 ≤ toeplitzEntry16737 a i j) ∧
    (∀ i₁ i₂ j₁ j₂,
      i₁ < i₂ → j₁ < j₂ →
        0 ≤
          toeplitzEntry16737 a i₁ j₁ * toeplitzEntry16737 a i₂ j₂ -
            toeplitzEntry16737 a i₁ j₂ * toeplitzEntry16737 a i₂ j₁)

/-- Independent finite vertex sets. -/
def independentSet16737 {V : Type*}
    (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → ¬ G.Adj u v

/-- The independence coefficient sequence of a finite simple graph. -/
noncomputable def independenceSequence16737 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ → ℝ :=
  fun k =>
    (Set.ncard {s : Finset V | independentSet16737 G s ∧ s.card = k} : ℝ)

/-- Disjoint union of two graph components. -/
def disjointUnionGraph16737 {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) :=
  SimpleGraph.sum G H

/-- Claim 16737: finite nonnegative log-concave sequences with no internal
zeros are closed under convolution; their Toeplitz matrices give the
corresponding TP2 characterization and TP2 multiplication law; and the
independence sequences of disjoint log-concave components remain log-concave
and unimodal. -/
def claim16737 : Prop :=
  (∀ a b : ℕ → ℝ,
    finiteSupport16737 a → finiteSupport16737 b →
    nonnegativeSequence16737 a → nonnegativeSequence16737 b →
    noInternalZeros16737 a → noInternalZeros16737 b →
    adjacentLogConcave16737 a → adjacentLogConcave16737 b →
      logConcaveSequence16737 (convolution16737 a b)) ∧
  (∀ a : ℕ → ℝ,
    finiteSupport16737 a →
    nonnegativeSequence16737 a →
    noInternalZeros16737 a →
      (adjacentLogConcave16737 a ↔ toeplitzTP2_16737 a)) ∧
  (∀ a b : ℕ → ℝ,
    finiteSupport16737 a → finiteSupport16737 b →
    toeplitzTP2_16737 a → toeplitzTP2_16737 b →
      toeplitzTP2_16737 (convolution16737 a b)) ∧
  (∀ {V W : Type*} [Fintype V] [Fintype W]
      (G : SimpleGraph V) (H : SimpleGraph W),
    (∀ n,
      independenceSequence16737 (disjointUnionGraph16737 G H) n =
        convolution16737 (independenceSequence16737 G)
          (independenceSequence16737 H) n) ∧
    (logConcaveSequence16737 (independenceSequence16737 G) →
      logConcaveSequence16737 (independenceSequence16737 H) →
        logConcaveSequence16737
            (independenceSequence16737 (disjointUnionGraph16737 G H)) ∧
          unimodalSequence16737
            (independenceSequence16737 (disjointUnionGraph16737 G H))))

end MathlibPlus.Open.ResearchFormalization
