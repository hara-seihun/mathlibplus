import MathlibPlus.Open.OracleAreaOccupation

namespace MathlibPlus.Open.ResearchFormalizationBatch.PosteriorCompletion

open Classical
open scoped BigOperators
open MathlibPlus.Open.OracleAreaOccupation

noncomputable section

abbrev PolicySeed (n : ℕ) := RandomizedPolicy n
abbrev CompleteTranscript (n : ℕ) := PolicySeed n × TranscriptState n

/-- The complete transcript carries the policy seed together with the revealed
coordinate assignments. -/
def transcriptState (c : CompleteTranscript n) : TranscriptState n := c.2

def childCompleteTranscript (c : CompleteTranscript n)
    (i : Unrevealed c.2) (ε : Sign) : CompleteTranscript n :=
  (c.1, child c.2 i.1 i.2 ε)

/-- The posterior mass of one completion in the cell of the preceding
complete transcript. -/
def posteriorCompletionWeight (h : TranscriptState n)
    (o : Configuration n) : ℝ :=
  if Consistent h o then
    ((2 : ℝ) ^ (n - h.1.card))⁻¹
  else 0

/-- The preceding posterior product law on two completions. -/
def precedingIndependentPairWeight (c : CompleteTranscript n)
    (o₀ o₁ : Configuration n) : ℝ :=
  posteriorCompletionWeight c.2 o₀ * posteriorCompletionWeight c.2 o₁

def observedAgreement (c : CompleteTranscript n)
    (i : Unrevealed c.2) (ε : Sign)
    (o₀ o₁ : Configuration n) : Prop :=
  o₀ i.1 = o₁ i.1 ∧ o₀ i.1 = ε

/-- The normalization mass of the agreement event in the preceding product
law, with the common observed sign fixed to the individual child. -/
def observedAgreementMass (c : CompleteTranscript n)
    (i : Unrevealed c.2) (ε : Sign) : ℝ :=
  ∑ o₀ : Configuration n, ∑ o₁ : Configuration n,
    if observedAgreement c i ε o₀ o₁ then
      precedingIndependentPairWeight c o₀ o₁
    else 0

/-- The posterior product law after the individual child has observed `ε`. -/
def childIndependentPairWeight (c : CompleteTranscript n)
    (i : Unrevealed c.2) (ε : Sign)
    (o₀ o₁ : Configuration n) : ℝ :=
  let childTranscript := childCompleteTranscript c i ε
  posteriorCompletionWeight childTranscript.2 o₀ *
    posteriorCompletionWeight childTranscript.2 o₁

/-- The preceding posterior product law conditioned on agreement at the newly
queried coordinate and on the observed common sign. -/
def agreementConditionedPairWeight (c : CompleteTranscript n)
    (i : Unrevealed c.2) (ε : Sign)
    (o₀ o₁ : Configuration n) : ℝ :=
  if observedAgreement c i ε o₀ o₁ then
    precedingIndependentPairWeight c o₀ o₁ /
      observedAgreementMass c i ε
  else 0

/-- After a fresh query, the child pair is the preceding posterior product law
conditioned on the two completions agreeing at that query and on their common
observed sign. -/
def claim47468_agreementConditionedChildPairLaw : Prop :=
  ∀ (n : ℕ) (seed : PolicySeed n) (h : TranscriptState n)
    (i : Unrevealed h) (ε : Sign)
    (o₀ o₁ : Configuration n),
    childIndependentPairWeight (seed, h) i ε o₀ o₁ =
      agreementConditionedPairWeight (seed, h) i ε o₀ o₁

end

end MathlibPlus.Open.ResearchFormalizationBatch.PosteriorCompletion
