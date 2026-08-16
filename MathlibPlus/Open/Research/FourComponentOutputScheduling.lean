import Mathlib

namespace MathlibPlus.Open.Research.FourComponentOutputScheduling

noncomputable section

open scoped BigOperators

abbrev Label := Fin 4
abbrev Output := Label → Bool
abbrev Observation := Label × Bool
abbrev State := Fin 4 → Option Observation
abbrev Policy := State → Option Label
abbrev OracleOutcome := Fin 5 → Bool
abbrev OracleLabel := Fin 5

/-- The sign represented by a Boolean output. -/
def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The four-component average `G`. -/
def outputMean (u : Output) : ℝ :=
  (∑ i : Label, signValue (u i)) / 4

def allNegative : Output := fun _ => false

def allPositive : Output := fun _ => true

/-- Exactly one sign differs from the other three. -/
def oneMinority (u : Output) : Prop :=
  (Finset.univ.filter (fun i : Label => u i = true)).card = 1 ∨
    (Finset.univ.filter (fun i : Label => u i = true)).card = 3

/-- The stated exchangeable dyadic law on four output signs. -/
noncomputable def dyadicWeight (u : Output) : ℝ := by
  classical
  exact
    if ∀ i : Label, u i = false then 3 / 8
    else if ∀ i : Label, u i = true then 3 / 8
    else if oneMinority u then 1 / 32
    else 0

/-- Compatibility of a transcript with an output completion. -/
def stateCompatible (s : State) (u : Output) : Prop :=
  ∀ q l b, s q = some (l, b) → u l = b

/-- Measurability of `G` under the stated law.  Completions of zero law are
not treated as possible completions. -/
def stateMeasurable (s : State) : Prop :=
  ∀ u v : Output,
    0 < dyadicWeight u →
      0 < dyadicWeight v →
        stateCompatible s u →
          stateCompatible s v → outputMean u = outputMean v

/-- Whether a label has already appeared in the transcript. -/
def labelRevealed (s : State) (i : Label) : Prop :=
  ∃ q b, s q = some (i, b)

/-- A deterministic adaptive policy using only previously revealed labels and
values.  A nonterminal choice is a fresh label; stopping is allowed precisely
when the target is measurable. -/
def legalPolicy (π : Policy) : Prop :=
  ∀ s : State,
    match π s with
    | none => stateMeasurable s
    | some i => ¬ labelRevealed s i

def emptyState : State := fun _ => none

/-- Append a fresh observation to the ordered transcript; a repeated label is
therefore deleted rather than recorded twice. -/
noncomputable def updateState (s : State) (i : Label) (b : Bool) : State := by
  classical
  exact
    if h : ∃ q : Fin 4, s q = none then
      Function.update s (Classical.choose h) (some (i, b))
    else s

/-- One policy step on an output completion. -/
def policyStep (π : Policy) (u : Output) (s : State) : State := by
  classical
  exact match π s with
    | none => s
    | some i => if labelRevealed s i then s else updateState s i (u i)

/-- The transcript after `n` policy steps. -/
def runState (π : Policy) (u : Output) : ℕ → State
  | 0 => emptyState
  | n + 1 => policyStep π u (runState π u n)

/-- Joint transcript mass for an independent internal randomizer. -/
def transcriptMass (p : Policy → ℝ) (j : ℕ) (s : State) : ℝ :=
  ∑ π : Policy, ∑ u : Output,
    if runState π u j = s then p π * dyadicWeight u else 0

/-- The unnormalized first posterior moment of `G`. -/
def transcriptFirstMoment (p : Policy → ℝ) (j : ℕ) (s : State) : ℝ :=
  ∑ π : Policy, ∑ u : Output,
    if runState π u j = s then
      p π * dyadicWeight u * outputMean u
    else 0

/-- The unnormalized second posterior moment of `G`. -/
def transcriptSecondMoment (p : Policy → ℝ) (j : ℕ) (s : State) : ℝ :=
  ∑ π : Policy, ∑ u : Output,
    if runState π u j = s then
      p π * dyadicWeight u * (outputMean u) ^ 2
    else 0

/-- Conditional variance on a transcript cell, with the zero-mass convention. -/
def conditionalTranscriptVariance
    (p : Policy → ℝ) (j : ℕ) (s : State) : ℝ :=
  let mass := transcriptMass p j s
  if mass = 0 then 0
  else
    transcriptSecondMoment p j s / mass -
      (transcriptFirstMoment p j s / mass) ^ 2

/-- Expected posterior variance after `j` distinct output reveals. -/
def expectedTranscriptVariance (p : Policy → ℝ) (j : ℕ) : ℝ :=
  ∑ s : State,
    transcriptMass p j s * conditionalTranscriptVariance p j s

/-- An arbitrary probability law on deterministic policies, independent of the
sign law. -/
def randomizedLegalPolicy (p : Policy → ℝ) : Prop :=
  (∀ π : Policy, 0 ≤ p π) ∧
    (∑ π : Policy, p π = 1) ∧
      (∀ π : Policy, p π > 0 → legalPolicy π)

/-- A full decision tree whose queried labels are five independent oracle
coordinates. -/
inductive FullQueryTree where
  | leaf : Bool → FullQueryTree
  | query : OracleLabel → FullQueryTree → FullQueryTree → FullQueryTree

/-- The output of a full query tree on an oracle outcome. -/
def evalFullQueryTree : FullQueryTree → OracleOutcome → Bool
  | FullQueryTree.leaf b, _ => b
  | FullQueryTree.query i left right, x =>
      if x i then evalFullQueryTree right x else evalFullQueryTree left x

/-- The query trace on one branch of a tree. -/
def queryTrace : FullQueryTree → OracleOutcome → List OracleLabel
  | FullQueryTree.leaf _, _ => []
  | FullQueryTree.query i left right, x =>
      i :: (if x i then queryTrace right x else queryTrace left x)

/-- Legality of a full five-query tree: every branch queries each coordinate
once and has five queries. -/
def legalFullQueryTree (t : FullQueryTree) : Prop :=
  ∀ x : OracleOutcome,
    (queryTrace t x).Nodup ∧ (queryTrace t x).length = 5

/-- The exact 12/12/one-fiber/zero-fiber partition of the product cube. -/
def assignmentFiberCounts (A : OracleOutcome → Output) : Prop :=
  Fintype.card {x : OracleOutcome // A x = allNegative} = 12 ∧
    Fintype.card {x : OracleOutcome // A x = allPositive} = 12 ∧
      (∀ u : Output, oneMinority u →
        Fintype.card {x : OracleOutcome // A x = u} = 1) ∧
        (∀ u : Output,
          (¬ (∀ i : Label, u i = false)) →
            (¬ (∀ i : Label, u i = true)) →
              ¬ oneMinority u →
                Fintype.card {x : OracleOutcome // A x = u} = 0)

/-- Each output coordinate is computed by a legal full five-query tree. -/
def coordinateFullQueryTrees (A : OracleOutcome → Output) : Prop :=
  ∀ i : Label, ∃ t : FullQueryTree,
    legalFullQueryTree t ∧
      ∀ x : OracleOutcome, evalFullQueryTree t x = A x i

/-- The uniform product-oracle weight. -/
def oracleWeight (_ : OracleOutcome) : ℝ := 1 / 32

/-- The mean of the four Boolean coordinate functions on one oracle outcome. -/
def productOracleMean (A : OracleOutcome → Output)
    (x : OracleOutcome) : ℝ :=
  (∑ i : Label, signValue (A x i)) / 4

/-- The product-oracle realization of the dyadic law. -/
def productOracleRealization : Prop :=
  ∃ A : OracleOutcome → Output,
    assignmentFiberCounts A ∧
      (∀ x : OracleOutcome, oracleWeight x = 1 / 32) ∧
        (∑ x : OracleOutcome, oracleWeight x = 1) ∧
          (∀ u : Output,
            (∑ x : OracleOutcome,
              if A x = u then oracleWeight x else 0) = dyadicWeight u) ∧
            coordinateFullQueryTrees A ∧
              (∀ x : OracleOutcome,
                productOracleMean A x = outputMean (A x))

/-- The exact four-component black-box output-scheduling obstruction. -/
def fourComponentBlackBoxOutputScheduling : Prop :=
  (∀ p : Policy → ℝ, randomizedLegalPolicy p →
    expectedTranscriptVariance p 0 = 13 / 16 ∧
      expectedTranscriptVariance p 1 = 39 / 256 ∧
        expectedTranscriptVariance p 2 = 13 / 224 ∧
          expectedTranscriptVariance p 3 = 3 / 208 ∧
            (∀ s : State,
              transcriptMass p 4 s ≠ 0 → stateMeasurable s) ∧
              expectedTranscriptVariance p 4 = 0 ∧
                expectedTranscriptVariance p 0 +
                    expectedTranscriptVariance p 1 +
                      expectedTranscriptVariance p 2 +
                        expectedTranscriptVariance p 3 = 24165 / 23296 ∧
                  24165 / 23296 = 1 + 869 / 23296 ∧
                    1 < 1 + 869 / 23296) ∧
  productOracleRealization

end

end MathlibPlus.Open.Research.FourComponentOutputScheduling
