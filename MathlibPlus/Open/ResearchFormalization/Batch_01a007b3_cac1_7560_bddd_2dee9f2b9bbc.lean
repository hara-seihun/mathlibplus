import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

/-- A finite sequence written in decreasing order. -/
def nonincreasing {n : ℕ} (v : Fin n → ℕ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i.1 ≤ j.1 → v j ≤ v i

/-- The sum of the first `k` entries, with a common zero padding length `n`. -/
def prefixSum {n : ℕ} (v : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ i, if i.1 < k then v i else 0

/-- Dominance order on two decreasing sequences of a common padded length. -/
def dominates {n : ℕ} (partA partB : Fin n → ℕ) : Prop :=
  (∑ i, partA i) = ∑ i, partB i ∧
    ∀ k ≤ n, prefixSum partB k ≤ prefixSum partA k

/-- The partition valuation associated to a function on the nonnegative reals. -/
def omegaPhi {n : ℕ} (φ : ℝ → ℝ) (v : Fin n → ℕ) : ℝ :=
  ∑ i, φ (v i : ℝ)

/-- The face selected by maximizing a partition valuation on a finite support. -/
def curvedInitialFace {n : ℕ} (S : Finset (Fin n → ℕ)) (φ : ℝ → ℝ) :
    Set (Fin n → ℕ) :=
  {v | v ∈ S ∧ ∀ w ∈ S, omegaPhi φ w ≤ omegaPhi φ v}

/-- A support consisting of decreasing partitions of one common total. -/
def admissibleSupport {n : ℕ} (S : Finset (Fin n → ℕ)) (t : ℕ) : Prop :=
  ∀ v ∈ S, nonincreasing v ∧ (∑ i, v i) = t

/-- Maximality for dominance among the partition coordinates in a support. -/
def dominanceMaximalIn {n : ℕ} (S : Finset (Fin n → ℕ)) (v : Fin n → ℕ) : Prop :=
  v ∈ S ∧ ∀ w ∈ S, dominates w v → w = v

/--
For partitions of one common nonnegative integer, strict convexity makes the
partition valuation monotone for dominance, with equality only for the same
padded partition. Consequently a curved initial face can contain only
incomparable dominance maxima.
-/
def convexPartitionDominanceClaim : Prop :=
  ∀ {n : ℕ} (partA partB : Fin n → ℕ),
    nonincreasing partA →
    nonincreasing partB →
    (∑ i, partA i) = ∑ i, partB i →
    dominates partA partB →
    ∀ φ : ℝ → ℝ,
      StrictConvexOn ℝ (Set.Ici (0 : ℝ)) φ →
      omegaPhi φ partA ≥ omegaPhi φ partB ∧
      (omegaPhi φ partA = omegaPhi φ partB → partA = partB) ∧
      ∀ (S : Finset (Fin n → ℕ)) (t : ℕ),
        admissibleSupport S t →
        (∀ v, v ∈ curvedInitialFace S φ → dominanceMaximalIn S v) ∧
        (∀ v w,
          v ∈ curvedInitialFace S φ →
          w ∈ curvedInitialFace S φ →
          v ≠ w →
          ¬ dominates v w ∧ ¬ dominates w v)

end MathlibPlus.Open.FormalizationBatch
