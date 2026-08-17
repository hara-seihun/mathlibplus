import MathlibPlus.Open.ResearchFormalization.CompletedThetaMonic11882

namespace MathlibPlus.Open.ResearchFormalization.CompletedTheta11883

noncomputable section

open MathlibPlus.Open.ResearchFormalization.CompletedTheta11882

/-- An entry has degree at most two in the initial moment parameter. -/
def realAtMostQuadratic (f : ℝ → ℝ) : Prop :=
  ∃ a b c : ℝ, ∀ t : ℝ, f t = a * t ^ 2 + b * t + c

/-- The exact completed-theta bulk, rather than an arbitrary matrix family, is
at most quadratic entrywise in its parameterized initial moment. -/
def checkerboardBulkAtMostQuadratic (h : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i j : Fin N,
    realAtMostQuadratic (fun t : ℝ => checkerboardBulk h t N i j)

/-- The entrywise derivative of the exact parameterized completed-theta bulk.
This is the polarized derivative carrier compared with the central difference. -/
def polarizedT0Derivative (h : ℕ → ℝ) (t0 : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => deriv (fun t : ℝ => checkerboardBulk h t N i j) t0

/-- A closed bounded real interval, represented by its set of points. -/
def closedRealInterval (I : Set ℝ) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ I = Set.Icc a b

abbrev realIntervalMatrix (N : ℕ) := Matrix (Fin N) (Fin N) (Set ℝ)

/-- Every entry of an interval matrix contains the corresponding exact value. -/
def intervalMatrixEncloses {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (I : realIntervalMatrix N) : Prop :=
  ∀ i j : Fin N, M i j ∈ I i j

/-- Entrywise overlap of two interval matrices. -/
def intervalMatricesOverlap {N : ℕ}
    (I J : realIntervalMatrix N) : Prop :=
  ∀ i j : Fin N, (I i j ∩ J i j).Nonempty

/-- The completed-theta derivative is the exact central difference, and sound
polarized and central-difference interval matrices overlap entrywise. -/
def exactDerivativeCrossCheck : Prop :=
  ∀ (h : ℕ → ℝ), completedXiEvenJet h →
    let t0 := 2 - 4 * h 0
    ∀ N : ℕ,
      checkerboardBulkAtMostQuadratic h N ∧
      (∀ t : ℝ,
        polarizedT0Derivative h t N = primitiveT0Derivative h t N) ∧
      (∀ (P C : realIntervalMatrix N),
        (∀ i j : Fin N, closedRealInterval (P i j)) →
        (∀ i j : Fin N, closedRealInterval (C i j)) →
        intervalMatrixEncloses (polarizedT0Derivative h t0 N) P →
        intervalMatrixEncloses (primitiveT0Derivative h t0 N) C →
        intervalMatricesOverlap P C)

end

end MathlibPlus.Open.ResearchFormalization.CompletedTheta11883
