import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4367Claim54298

noncomputable section

def finiteExpectation {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω, weight ω * f ω

def probabilityWeights {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) : Prop :=
  (∀ ω, 0 ≤ weight ω) ∧ ∑ ω, weight ω = 1

def conditionalVariance {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (g : Ω → ℝ) : ℝ :=
  finiteExpectation weight (fun ω =>
    (g ω - finiteExpectation weight g) ^ 2)

def signOfBool (b : Bool) : ℝ := if b then 1 else -1

def parityDecoyValue (k n : ℕ)
    (ω : (Fin k → Bool) × (Fin n → Bool)) : ℝ :=
  (∏ i : Fin k, signOfBool (ω.1 i)) / 2 +
    (∑ j : Fin n, signOfBool (ω.2 j)) / (2 * (n : ℝ))

def decoyCellWeight {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool)
    (ω : (Fin k → Bool) × (Fin n → Bool)) : ℝ :=
  if _ : ∀ j, j ∈ D → ω.2 j = observed j then
    ((2 : ℝ) ^ (k + n - D.card))⁻¹
  else 0

def observedDecoySum {n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool) : ℝ :=
  ∑ j ∈ D, signOfBool (observed j)

def parityDecoyBaseline {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool)
    (q : Fin (k + 1)) : ℝ :=
  if q.val = 0 then 0 else observedDecoySum D observed / (2 * (n : ℝ))

def parityRollbackCurve {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool)
    (q : Fin (k + 1)) : ℝ :=
  finiteExpectation (decoyCellWeight D observed)
    (fun ω =>
      (parityDecoyValue k n ω -
        parityDecoyBaseline D observed q) ^ 2)

def parityConditionalVariance {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool) : ℝ :=
  conditionalVariance (decoyCellWeight (k := k) D observed)
    (parityDecoyValue k n)

def lowerEnvelope {k : ℕ} (h : Fin (k + 1) → ℝ) : ℝ :=
  sInf (Set.range h)

def parityCellWeightAfter {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool)
    (l : Fin k) (b : Bool)
    (ω : (Fin k → Bool) × (Fin n → Bool)) : ℝ :=
  if _ : (∀ j, j ∈ D → ω.2 j = observed j) ∧ ω.1 l = b then
    ((2 : ℝ) ^ (k + n - D.card - 1))⁻¹
  else 0

def decoyCellWeightAfter {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool)
    (j : Fin n) (b : Bool)
    (ω : (Fin k → Bool) × (Fin n → Bool)) : ℝ :=
  decoyCellWeight (insert j D) (fun i => if i = j then b else observed i) ω

def decoyRollbackCurve {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool)
    (j : Fin n) (b : Bool) (q : Fin (k + 1)) : ℝ :=
  finiteExpectation (decoyCellWeightAfter D observed j b)
    (fun ω =>
      (parityDecoyValue k n ω -
        (if q.val = 0 then 0 else
          (observedDecoySum D observed + signOfBool b) /
            (2 * (n : ℝ)))) ^ 2)

def parityAfterRollbackCurve {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool)
    (l : Fin k) (b : Bool) (q : Fin (k + 1)) : ℝ :=
  finiteExpectation (parityCellWeightAfter D observed l b)
    (fun ω =>
      (parityDecoyValue k n ω -
        parityDecoyBaseline D observed q) ^ 2)

def weightedPotential {k : ℕ}
    (w : Fin (k + 1) → ℝ) (h : Fin (k + 1) → ℝ) : ℝ :=
  ∑ q : Fin (k + 1), w q * h q

def positiveTailWeight {k : ℕ} (w : Fin (k + 1) → ℝ) : ℝ :=
  ∑ q : Fin k, w q.succ

def weightedDecoyScore {k n : ℕ}
    (w : Fin (k + 1) → ℝ)
    (D : Finset (Fin n)) (observed : Fin n → Bool) (j : Fin n) : ℝ :=
  weightedPotential w (parityRollbackCurve (k := k) D observed) -
    (weightedPotential w (decoyRollbackCurve (k := k) D observed j false) +
      weightedPotential w (decoyRollbackCurve (k := k) D observed j true)) / 2

def weightedParityScore {k n : ℕ}
    (w : Fin (k + 1) → ℝ)
    (D : Finset (Fin n)) (observed : Fin n → Bool) (l : Fin k) : ℝ :=
  weightedPotential w (parityRollbackCurve (k := k) D observed) -
    (weightedPotential w (parityAfterRollbackCurve (k := k) D observed l false) +
      weightedPotential w (parityAfterRollbackCurve (k := k) D observed l true)) / 2

def lowerEnvelopeDecoyScore {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool) (j : Fin n) : ℝ :=
  lowerEnvelope (k := k) (parityRollbackCurve D observed) -
    (lowerEnvelope (k := k) (decoyRollbackCurve D observed j false) +
      lowerEnvelope (k := k) (decoyRollbackCurve D observed j true)) / 2

def lowerEnvelopeParityScore {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool) (l : Fin k) : ℝ :=
  lowerEnvelope (k := k) (parityRollbackCurve D observed) -
    (lowerEnvelope (k := k) (parityAfterRollbackCurve D observed l false) +
      lowerEnvelope (k := k) (parityAfterRollbackCurve D observed l true)) / 2

abbrev QueryCoordinate (n k : ℕ) := Sum (Fin n) (Fin k)

def weightedCellScore {k n : ℕ}
    (w : Fin (k + 1) → ℝ) (D : Finset (Fin n))
    (observed : Fin n → Bool) : QueryCoordinate n k → ℝ
  | Sum.inl j => weightedDecoyScore (k := k) w D observed j
  | Sum.inr l => weightedParityScore (k := k) w D observed l

def lowerEnvelopeCellScore {k n : ℕ}
    (D : Finset (Fin n)) (observed : Fin n → Bool) : QueryCoordinate n k → ℝ
  | Sum.inl j => lowerEnvelopeDecoyScore (k := k) D observed j
  | Sum.inr l => lowerEnvelopeParityScore (k := k) D observed l

def queryBefore {n k : ℕ}
    (query : Fin (n + k) → QueryCoordinate n k)
    (t : Fin (n + k)) : Finset (QueryCoordinate n k) :=
  (Finset.univ : Finset (Fin t.val)).image
    (fun u => query ⟨u.val, lt_trans u.isLt t.isLt⟩)

def decoyLabelsBefore {n k : ℕ}
    (query : Fin (n + k) → QueryCoordinate n k)
    (t : Fin (n + k)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun j => ∃ u : Fin t.val,
      query ⟨u.val, lt_trans u.isLt t.isLt⟩ = Sum.inl j)

def positiveScorePath {n k : ℕ}
    (score : Finset (Fin n) → (Fin n → Bool) → QueryCoordinate n k → ℝ)
    (query : Fin (n + k) → QueryCoordinate n k)
    (ω : (Fin k → Bool) × (Fin n → Bool)) : Prop :=
  Function.Injective query ∧
    ∀ t : Fin (n + k),
      (∃ c : QueryCoordinate n k,
        c ∉ queryBefore query t ∧
        0 < score (decoyLabelsBefore query t) ω.2 c) →
      0 < score (decoyLabelsBefore query t) ω.2 (query t)

def firstNQueriesAreDecoys {n k : ℕ}
    (query : Fin (n + k) → QueryCoordinate n k) : Prop :=
  ∀ t : Fin n, ∃ j : Fin n, query (Fin.castAdd k t) = Sum.inl j

def exactScoreSeparationClaim54298 : Prop :=
  ∀ (k n : ℕ) (D : Finset (Fin n)) (observed : Fin n → Bool)
    (w : Fin (k + 1) → ℝ),
    D.card < n → 2 ≤ k → 1 ≤ n →
    (∀ q : Fin (k + 1), 0 ≤ w q) →
    0 < positiveTailWeight w →
    (∀ j : Fin n, j ∉ D →
      weightedDecoyScore w D observed j =
        positiveTailWeight w / (4 * (n : ℝ) ^ 2) ∧
      lowerEnvelopeDecoyScore (k := k) D observed j =
        1 / (4 * (n : ℝ) ^ 2) ∧
      0 < weightedDecoyScore w D observed j ∧
      0 < lowerEnvelopeDecoyScore (k := k) D observed j) ∧
    (∀ l : Fin k,
      weightedParityScore w D observed l = 0 ∧
      lowerEnvelopeParityScore (k := k) D observed l = 0) ∧
    (∀ query : Fin (n + k) → QueryCoordinate n k,
      ∀ ω : (Fin k → Bool) × (Fin n → Bool),
      (positiveScorePath (weightedCellScore w) query ω ∨
        positiveScorePath (lowerEnvelopeCellScore) query ω) →
      firstNQueriesAreDecoys query)

end
end MathlibPlus.Open.ResearchFormalization.R4367Claim54298
