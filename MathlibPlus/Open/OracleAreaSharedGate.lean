import Mathlib

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.OracleAreaSharedGate

noncomputable section

abbrev SignConfig (n : ℕ) := Fin (n + 1) → Bool

def zeroIndex (n : ℕ) : Fin (n + 1) :=
  ⟨0, Nat.succ_pos n⟩

def signValue (b : Bool) : ℝ :=
  if b = true then 1 else -1

def coordinateComponent (n : ℕ) (j : Fin n) (ω : SignConfig n) : ℝ :=
  if ω (zeroIndex n) = false then -1 else signValue (ω j.succ)

def depthTwoTreeValue (n : ℕ) (j : Fin n) (ω : SignConfig n) : ℝ :=
  if signValue (ω j.succ) = -1 then -1 else signValue (ω (zeroIndex n))

def uniformSignExpectation (n : ℕ) (f : SignConfig n → ℝ) : ℝ :=
  (∑ ω : SignConfig n, f ω) / (2 : ℝ) ^ (n + 1)

def mixtureMean (n : ℕ) (ω : SignConfig n) : ℝ :=
  (∑ j : Fin n, coordinateComponent n j ω) / (n : ℝ)

def approximationResidual (n r : ℕ) (h : r ≤ n) (a : Fin (r + 1) → ℝ)
    (ω : SignConfig n) : ℝ :=
  mixtureMean n ω - a 0 -
    ∑ j : Fin r, a j.succ * coordinateComponent n (j.castLE h) ω

noncomputable def spanDistanceSquared (n r : ℕ) : ℝ :=
  if h : r ≤ n then
    sInf {v : ℝ |
      ∃ a : Fin (r + 1) → ℝ,
        v = uniformSignExpectation n
          (fun ω => (approximationResidual n r h a ω) ^ 2)}
  else 0

def harmonicNumber (m : ℕ) : ℝ :=
  ∑ q ∈ Finset.range m, 1 / ((q + 1 : ℕ) : ℝ)

def spanClosedForm (n r : ℕ) : ℝ :=
  ((n + 2 : ℕ) : ℝ) * ((n - r : ℕ) : ℝ) /
    (2 * (n : ℝ) ^ 2 * ((r + 2 : ℕ) : ℝ))

def spanTail (n : ℕ) : ℝ :=
  ∑ r ∈ Finset.range n, spanDistanceSquared n r

def spanTailClosedForm (n : ℕ) : ℝ :=
  ((n + 2 : ℕ) : ℝ) / (2 * (n : ℝ) ^ 2) *
    (((n + 2 : ℕ) : ℝ) * (harmonicNumber (n + 1) - 1) - (n : ℝ))

def targetAwareTranscript (n m : ℕ) (ω : SignConfig n) :
    Fin (n + 1) → Option Bool :=
  fun i =>
    if m = 0 then none
    else if i = zeroIndex n then some (ω i)
    else if ω (zeroIndex n) = false then none
    else if i.val < m then some (ω i)
    else none

noncomputable def targetCellVariance (n m : ℕ) (ω : SignConfig n) : ℝ :=
  let cell : Finset (SignConfig n) :=
    Finset.univ.filter (fun η =>
      targetAwareTranscript n m η = targetAwareTranscript n m ω)
  let cellMean : ℝ :=
    (∑ η ∈ cell, mixtureMean n η) / (cell.card : ℝ)
  (∑ η ∈ cell, (mixtureMean n η - cellMean) ^ 2) / (cell.card : ℝ)

def targetPosteriorVarianceAt (n m : ℕ) : ℝ :=
  uniformSignExpectation n (targetCellVariance n m)

noncomputable def targetAwarePosteriorVarianceArea (n : ℕ) : ℝ :=
  ∑' m : ℕ, targetPosteriorVarianceAt n m

def sharedGateCounterexample : Prop :=
  (∀ n : ℕ, 2 ≤ n →
    (∀ j : Fin n, ∀ ω : SignConfig n,
      depthTwoTreeValue n j ω = coordinateComponent n j ω) ∧
    (∀ r : ℕ, r ≤ n →
      spanDistanceSquared n r = spanClosedForm n r) ∧
    spanTail n = spanTailClosedForm n ∧
    Tendsto
      (fun k : ℕ => spanTail k / ((1 / 2 : ℝ) * Real.log (k : ℝ)))
      atTop (𝓝 1) ∧
    (∀ C : ℝ, ∃ k : ℕ, 2 ≤ k ∧ C < spanTail k) ∧
    targetAwarePosteriorVarianceArea n =
      (2 * (n : ℝ) + 3) / (4 * (n : ℝ)) ∧
    (2 * (n : ℝ) + 3) / (4 * (n : ℝ)) < 1) ∧
  (∀ C : ℝ, ∃ n : ℕ, 2 ≤ n ∧ C < spanTail n)

end

end MathlibPlus.Open.OracleAreaSharedGate
