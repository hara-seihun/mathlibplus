import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Research.AdaptiveOracleAreaSharp

abbrev Sign := Fin 2
abbrev Outcome := Fin 4 → Sign
abbrev History := Fin 4 → Option Sign
abbrev Policy := History → Option (Fin 4)

def signValue (s : Sign) : ℝ := if s = 0 then -1 else 1

def coordinate (i : Fin 4) (ω : Outcome) : ℝ := signValue (ω i)

def nextIndex (i : Fin 4) : Fin 4 := i + 1

def previousIndex (i : Fin 4) : Fin 4 := i + 3

def h (i : Fin 4) (ω : Outcome) : ℝ :=
  if coordinate i ω = 1 then coordinate (nextIndex i) ω
  else coordinate (previousIndex i) ω

def hSecondQuery (i : Fin 4) (s : Sign) : Fin 4 :=
  if signValue s = 1 then nextIndex i else previousIndex i

def hTreeEvaluation (i : Fin 4) (ω : Outcome) : ℝ :=
  signValue (ω (hSecondQuery i (ω i)))

def hTreeComputes : Prop :=
  ∀ i : Fin 4, ∀ ω : Outcome, hTreeEvaluation i ω = h i ω

def uniformExpectation (f : Outcome → ℝ) : ℝ :=
  (Fintype.card Outcome : ℝ)⁻¹ * ∑ ω : Outcome, f ω

def eventProbability (event : Outcome → Prop) : ℝ :=
  letI : ∀ ω, Decidable (event ω) :=
    fun ω => Classical.propDecidable (event ω)
  (Fintype.card Outcome : ℝ)⁻¹ *
    ((Finset.univ.filter event).card : ℝ)

def independentUniformCoordinates : Prop :=
  (∀ i : Fin 4, ∀ s : Sign,
    eventProbability (fun ω => ω i = s) = (1 : ℝ) / 2) ∧
  (∀ x : Outcome,
    eventProbability (fun ω => ∀ i : Fin 4, ω i = x i) = (1 : ℝ) / 16)

def initialHistory : History := fun _ => none

def compatible (history : History) (ω : Outcome) : Prop :=
  ∀ i : Fin 4, ∀ s : Sign, history i = some s → ω i = s

def compatibleOutcomes (history : History) : Finset Outcome :=
  letI : ∀ ω, Decidable (compatible history ω) :=
    fun ω => Classical.propDecidable (compatible history ω)
  Finset.univ.filter (fun ω => compatible history ω)

def averageOn (f : Outcome → ℝ) (s : Finset Outcome) : ℝ :=
  if s.Nonempty then
    (s.card : ℝ)⁻¹ * s.sum f
  else 0

def varianceOn (f : Outcome → ℝ) (s : Finset Outcome) : ℝ :=
  averageOn (fun ω => (f ω - averageOn f s) ^ 2) s

def posteriorVariance (f : Outcome → ℝ) (history : History) : ℝ :=
  varianceOn f (compatibleOutcomes history)

def observe (history : History) (ω : Outcome) (q : Fin 4) : History :=
  Function.update history q (some (ω q))

def historyAt (policy : Policy) (ω : Outcome) : ℕ → History
  | 0 => initialHistory
  | m + 1 =>
      let history := historyAt policy ω m
      match policy history with
      | none => history
      | some q => observe history ω q

def legalPolicy (policy : Policy) : Prop :=
  ∀ history : History, ∀ q : Fin 4,
    policy history = some q → history q = none

def revealsAll (policy : Policy) : Prop :=
  ∀ ω : Outcome, ∃ m : ℕ, ∀ i : Fin 4,
    historyAt policy ω m i = some (ω i)

def validWeights (p : Fin 4 → ℝ) : Prop :=
  (∀ i : Fin 4, 0 ≤ p i) ∧ ∑ i : Fin 4, p i = 1

def g (p : Fin 4 → ℝ) (ω : Outcome) : ℝ :=
  ∑ i : Fin 4, p i * h i ω

def policyArea (p : Fin 4 → ℝ) (policy : Policy) : ℝ :=
  ∑' m : ℕ,
    uniformExpectation
      (fun ω => posteriorVariance (g p) (historyAt policy ω m))

def hasAreaAtMostTwo (p : Fin 4 → ℝ) : Prop :=
  ∃ policy : Policy,
    legalPolicy policy ∧
    revealsAll policy ∧
    policyArea p policy ≤ 2

def vertexWeights (i : Fin 4) : Fin 4 → ℝ :=
  fun j => if j = i then 1 else 0

def vertexSharpAtTwo (i : Fin 4) : Prop :=
  (∀ policy : Policy,
    legalPolicy policy →
    revealsAll policy →
    2 ≤ policyArea (vertexWeights i) policy) ∧
  (∃ policy : Policy,
    legalPolicy policy ∧
    revealsAll policy ∧
    (∀ ω : Outcome, g (vertexWeights i) ω = h i ω) ∧
    policyArea (vertexWeights i) policy = 2)

def claim60169 : Prop :=
  independentUniformCoordinates ∧
  hTreeComputes ∧
  (∀ p : Fin 4 → ℝ, validWeights p → hasAreaAtMostTwo p) ∧
  (∀ i : Fin 4, vertexSharpAtTwo i)

end MathlibPlus.Open.Research.AdaptiveOracleAreaSharp
