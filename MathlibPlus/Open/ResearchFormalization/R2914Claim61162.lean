import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2914Claim61162

open scoped BigOperators
noncomputable section

private abbrev Label := Fin 9
private abbrev Sample := Bool × (Label → Bool) × (Label → Bool)
private abbrev Transcript := Label → Option (Fin 10 × Bool)
private abbrev Policy := Transcript → Option Label

private def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

private def selectorOutput (i : Label) (ω : Sample) : Bool :=
  if ω.2.1 i then ω.1 else ω.2.2 i

private def target (ω : Sample) : ℝ :=
  (∑ i : Label, signValue (selectorOutput i ω)) / 9

private def sampleWeight (_ω : Sample) : ℝ :=
  1 / (Fintype.card Sample : ℝ)

private def emptyTranscript : Transcript :=
  fun _ => none

private def observe
    (h : Transcript) (r : Fin 10) (i : Label) (b : Bool) : Transcript :=
  Function.update h i (some (r, b))

private def runTranscript (π : Policy) (ω : Sample) : ℕ → Transcript
  | 0 => emptyTranscript
  | r + 1 =>
      let h := runTranscript π ω r
      match π h with
      | none => h
      | some i => observe h (Fin.ofNat 10 r) i (selectorOutput i ω)

private def labelRevealed (h : Transcript) (i : Label) : Prop :=
  ∃ r b, h i = some (r, b)

private def transcriptCompatible (h : Transcript) (ω : Sample) : Prop :=
  ∀ i r b, h i = some (r, b) → selectorOutput i ω = b

private def targetMeasurable (h : Transcript) : Prop :=
  ∀ ω ω' : Sample,
    transcriptCompatible h ω →
      transcriptCompatible h ω' →
        target ω = target ω'

private def legalPolicy (π : Policy) : Prop :=
  ∀ h : Transcript,
    match π h with
    | none => targetMeasurable h
    | some i => ¬ labelRevealed h i

private def randomizedLegalPolicy (p : Policy → ℝ) : Prop :=
  (∀ π : Policy, 0 ≤ p π) ∧
    (∑ π : Policy, p π = 1) ∧
      (∀ π : Policy, p π > 0 → legalPolicy π)

private def transcriptMass
    (p : Policy → ℝ) (r : ℕ) (h : Transcript) : ℝ :=
  ∑ π : Policy, ∑ ω : Sample,
    if runTranscript π ω r = h then
      p π * sampleWeight ω
    else 0

private def transcriptFirstMoment
    (p : Policy → ℝ) (r : ℕ) (h : Transcript) : ℝ :=
  ∑ π : Policy, ∑ ω : Sample,
    if runTranscript π ω r = h then
      p π * sampleWeight ω * target ω
    else 0

private def transcriptSecondMoment
    (p : Policy → ℝ) (r : ℕ) (h : Transcript) : ℝ :=
  ∑ π : Policy, ∑ ω : Sample,
    if runTranscript π ω r = h then
      p π * sampleWeight ω * (target ω) ^ 2
    else 0

private def conditionalTranscriptVariance
    (p : Policy → ℝ) (r : ℕ) (h : Transcript) : ℝ :=
  let mass := transcriptMass p r h
  if mass = 0 then 0
  else
    transcriptSecondMoment p r h / mass -
      (transcriptFirstMoment p r h / mass) ^ 2

private def expectedTranscriptVariance
    (p : Policy → ℝ) (r : ℕ) : ℝ :=
  ∑ h : Transcript,
    transcriptMass p r h * conditionalTranscriptVariance p r h

private def outputArea (p : Policy → ℝ) : ℝ :=
  ∑ r : Fin 9, expectedTranscriptVariance p r.val

private def coefficientOneComponentOutputScheduling : Prop :=
  ∀ p : Policy → ℝ,
    randomizedLegalPolicy p → outputArea p ≤ 1

private def blackBoxOutputSchedulingValues : Prop :=
  ∀ p : Policy → ℝ,
    randomizedLegalPolicy p →
      expectedTranscriptVariance p 0 = 1 / 3 ∧
      expectedTranscriptVariance p 1 = 2 / 9 ∧
      expectedTranscriptVariance p 2 = 7 / 45 ∧
      expectedTranscriptVariance p 3 = 55 / 504 ∧
      expectedTranscriptVariance p 4 = 85 / 1107 ∧
      expectedTranscriptVariance p 5 = 1223 / 23058 ∧
      expectedTranscriptVariance p 6 = 4747 / 134685 ∧
      expectedTranscriptVariance p 7 = 306599 / 14414544 ∧
      expectedTranscriptVariance p 8 = 2607457 / 265140891 ∧
      expectedTranscriptVariance p 9 = 0 ∧
      outputArea p = 1678534947568537 / 1651431807199440 ∧
      outputArea p = 1 + 27103140369097 / 1651431807199440 ∧
      1 < outputArea p

/-- The exact nine-selector black-box posterior-variance obstruction. -/
def blackBoxComponentOutputScheduling_claim61162 : Prop :=
  blackBoxOutputSchedulingValues ∧
    ¬ coefficientOneComponentOutputScheduling

end
end MathlibPlus.Open.ResearchFormalization.R2914Claim61162
