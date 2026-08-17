import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.R3193

noncomputable section

/-- The finite product of the shared bit and the three private bit families. -/
structure RademacherSample (n : ℕ) where
  a : Bool
  u : Fin n → Bool
  v : Fin n → Bool
  b : Fin n → Bool
  deriving Fintype, DecidableEq

/-- A complete component transcript records exactly the queried branch bits and
its returned bit.  On the common branch the returned bit is the shared bit; on
both private branches it is the component's private answer bit. -/
structure ComponentTranscript where
  u : Bool
  v : Option Bool
  answer : Bool
  deriving DecidableEq

def rademacherValue (x : Bool) : ℝ :=
  if x = true then 1 else -1

def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (1 / (Fintype.card α : ℝ)) * ∑ x : α, f x

def commonIndicator (n : ℕ) (j : Fin n) (ω : RademacherSample n) : ℝ :=
  if ω.u j = true ∧ ω.v j = true then 1 else 0

def componentValue (n : ℕ) (j : Fin n) (ω : RademacherSample n) : ℝ :=
  commonIndicator n j ω * rademacherValue ω.a +
    (1 - commonIndicator n j ω) * rademacherValue (ω.b j)

def componentTranscript (n : ℕ) (j : Fin n) (ω : RademacherSample n) : ComponentTranscript :=
  if ω.u j = true then
    { u := true
      v := some (ω.v j)
      answer := if ω.v j = true then ω.a else ω.b j }
  else
    { u := false
      v := none
      answer := ω.b j }

def transcriptValue (τ : ComponentTranscript) : ℝ :=
  rademacherValue τ.answer

def transcriptQueryCount (n : ℕ) (j : Fin n) (ω : RademacherSample n) : ℕ :=
  if ω.u j = true then 3 else 2

def conditionalAverage {α β : Type*} [Fintype α] [DecidableEq β]
    (Y : α → β) (f : α → ℝ) (ω : α) : ℝ := by
  classical
  let fibre := (Finset.univ : Finset α).filter (fun η => Y η = Y ω)
  exact (1 / (fibre.card : ℝ)) * fibre.sum f

def uniformVariance {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformAverage (fun ω => (f ω - uniformAverage f) ^ 2)

def commonBranchProbability (n : ℕ) (j : Fin n) : ℝ :=
  uniformAverage (commonIndicator n j)

def conditionalVariance {α β : Type*} [Fintype α] [DecidableEq β]
    (Y : α → β) (f : α → ℝ) (ω : α) : ℝ :=
  conditionalAverage Y
    (fun η => (f η - conditionalAverage Y f ω) ^ 2) ω

def componentMean (n : ℕ) (j : Fin n) : ℝ :=
  uniformAverage (componentValue n j)

def componentVariance (n : ℕ) (j : Fin n) : ℝ :=
  uniformVariance (componentValue n j)

def componentCovariance (n : ℕ) (j k : Fin n) : ℝ :=
  uniformAverage (fun ω =>
    (componentValue n j ω - componentMean n j) *
      (componentValue n k ω - componentMean n k))

def mu (n : ℕ) (ω : RademacherSample n) : ℝ :=
  (1 / (n : ℝ)) * ∑ j : Fin n, componentValue n j ω

def V (n : ℕ) : ℝ :=
  uniformVariance (mu n)

def W (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ j : Fin n, componentVariance n j

def posteriorComponentMean (n : ℕ) (j l : Fin n)
    (ω : RademacherSample n) : ℝ :=
  conditionalAverage (componentTranscript n j) (componentValue n l) ω

def posteriorComponentVariance (n : ℕ) (j l : Fin n)
    (ω : RademacherSample n) : ℝ :=
  conditionalVariance (componentTranscript n j) (componentValue n l) ω

def posteriorW (n : ℕ) (j : Fin n) (ω : RademacherSample n) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ l : Fin n, posteriorComponentVariance n j l ω

def deltaW (n : ℕ) (j : Fin n) : ℝ :=
  W n - uniformAverage (posteriorW n j)

def posteriorMuVariance (n : ℕ) (j : Fin n) (ω : RademacherSample n) : ℝ :=
  conditionalVariance (componentTranscript n j) (mu n) ω

def deltaV (n : ℕ) (j : Fin n) : ℝ :=
  V n - uniformAverage (posteriorMuVariance n j)

def fullBlockScore (n : ℕ) (j : Fin n) : ℝ :=
  deltaW n j + deltaV n j

def averageFullBlockScore (n : ℕ) : ℝ :=
  uniformAverage (fullBlockScore n)

def p : ℝ := 1 / 4

/-- Claim 47053: the explicit shared-bit Rademacher construction at nine
components gives a strict counterexample to both complete-component pivot
inequalities. -/
def claim47053 : Prop :=
  p = 1 / 4 ∧
  (∀ j : Fin 9,
    commonBranchProbability 9 j = p ∧
    V 9 = 1 / 6 ∧
    deltaW 9 j = 1 / 8 ∧
    deltaV 9 j = 1 / 27 ∧
    fullBlockScore 9 j = 35 / 216 ∧
    fullBlockScore 9 j = V 9 - 1 / 216 ∧
    fullBlockScore 9 j < V 9 ∧
    (∀ ω : RademacherSample 9,
      componentValue 9 j ω = transcriptValue (componentTranscript 9 j ω)) ∧
    (∀ ω : RademacherSample 9,
      transcriptQueryCount 9 j ω ≤ 3)) ∧
  (∀ j k : Fin 9, fullBlockScore 9 j = fullBlockScore 9 k) ∧
  averageFullBlockScore 9 = 35 / 216 ∧
  averageFullBlockScore 9 < V 9 ∧
  ¬ (∃ j : Fin 9, fullBlockScore 9 j ≥ V 9) ∧
  ¬ (averageFullBlockScore 9 ≥ V 9)

end

end MathlibPlus.Open.Research.R3193
