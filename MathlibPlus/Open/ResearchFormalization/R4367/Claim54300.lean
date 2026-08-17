import MathlibPlus.Open.ResearchFormalization.R4367.Claim54297
import MathlibPlus.Open.ResearchFormalization.R4367.Claim54298

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4367Claim54300

open MathlibPlus.Open.ResearchFormalization.R4367Claim54298

noncomputable section

/-- The first `r` decoy coordinates in the exact finite parity--decoy model. -/
def prefixDecoySet54300 {n : ℕ} (r : Fin (n + 1)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun j => j.val < r.val)

def observedDecoys54300 {n : ℕ} : Fin n → Bool :=
  fun _ => false

def forcedVariance54300 (k n : ℕ) (r : Fin (n + 1)) : ℝ :=
  parityConditionalVariance (k := k) (n := n)
    (prefixDecoySet54300 r) observedDecoys54300

def forcedLowerEnvelope54300 (k n : ℕ) (r : Fin (n + 1)) : ℝ :=
  lowerEnvelope (k := k)
    (parityRollbackCurve (k := k) (n := n)
      (prefixDecoySet54300 r) observedDecoys54300)

def baseVariance54300 (n r : ℕ) : ℝ :=
  1 / 4 + ((n - r : ℕ) : ℝ) / (4 * (n : ℝ) ^ 2)

/-- The component depths are those of the parity component and the n literal
components in the supplied mixture, rather than an unconstrained depth value. -/
def forcedStateFormula54300 : Prop :=
  ∀ (k n r : ℕ) (D : Finset (Fin n)) (observed : Fin n → Bool),
    D.card = r → r ≤ n → 2 ≤ k → 1 ≤ n →
      parityConditionalVariance (k := k) (n := n) D observed =
          baseVariance54300 n r ∧
        lowerEnvelope (k := k)
            (parityRollbackCurve (k := k) (n := n) D observed) =
          baseVariance54300 n r

def componentDepth54300 (k _n : ℕ) (c : Fin (_n + 1)) : ℕ :=
  if c.val = 0 then k else 1

def maximumComponentDepth54300 (k _n : ℕ) : ℕ :=
  max k 1

def rootInclusiveOccupation54300 (k n : ℕ) : ℝ :=
  ∑ r : Fin n, forcedVariance54300 k n r.castSucc

def postQueryOccupation54300 (k n : ℕ) : ℝ :=
  ∑ r : Fin (n + 1),
    if r.val = 0 then 0 else forcedVariance54300 k n r

def lowerEnvelopeOccupation54300 (k n : ℕ) : ℝ :=
  ∑ r : Fin n, forcedLowerEnvelope54300 k n r.castSucc

def rootClosedSum54300 (n : ℕ) : ℝ :=
  (n : ℝ) / 4 + ((n + 1 : ℕ) : ℝ) / (8 * (n : ℝ))

def postClosedSum54300 (n : ℕ) : ℝ :=
  (n : ℝ) / 4 + ((n - 1 : ℕ) : ℝ) / (8 * (n : ℝ))

def noUniversalDepthBound54300 : Prop :=
  ¬ ∃ C : ℝ, ∀ (k n : ℕ),
    2 ≤ k → 1 ≤ n →
      rootInclusiveOccupation54300 k n ≤
        C * (maximumComponentDepth54300 k n : ℝ)

/-- Claim 54300: the exact conditional variance and both occupation conventions
are summed over the actual parity--decoy carrier, while the weighted and
lower-envelope policy class is the positive-score class from Claim 54298. -/
def forcedAreaAndOccupationClaim54300 : Prop :=
  forcedStateFormula54300 ∧
    exactScoreSeparationClaim54298 ∧
    (∀ (k n : ℕ), 2 ≤ k → 1 ≤ n →
      (∀ r : Fin (n + 1),
        forcedVariance54300 k n r = baseVariance54300 n r.val) ∧
      rootInclusiveOccupation54300 k n = rootClosedSum54300 n ∧
      postQueryOccupation54300 k n = postClosedSum54300 n ∧
      lowerEnvelopeOccupation54300 k n = rootInclusiveOccupation54300 k n ∧
      (n : ℝ) / 4 ≤ rootInclusiveOccupation54300 k n ∧
      (n : ℝ) / 4 ≤ postQueryOccupation54300 k n ∧
      (∀ c : Fin (n + 1),
        componentDepth54300 k n c ≤ maximumComponentDepth54300 k n) ∧
      componentDepth54300 k n 0 = k ∧
      maximumComponentDepth54300 k n = k) ∧
    noUniversalDepthBound54300

end

end MathlibPlus.Open.ResearchFormalization.R4367Claim54300
