import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4367Claim54297

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

def parityLiteralDecoyClaim54297 : Prop :=
  ∀ (k n r : ℕ) (D : Finset (Fin n)) (observed : Fin n → Bool),
    D.card = r → r ≤ n → 2 ≤ k → 1 ≤ n →
    let h := parityRollbackCurve (k := k) D observed
    let weight := decoyCellWeight (k := k) D observed
    let variance := parityConditionalVariance (k := k) D observed
    let S := observedDecoySum D observed
    let base : ℝ := 1 / 4 + ((n - r : ℕ) : ℝ) / (4 * (n : ℝ) ^ 2)
    probabilityWeights weight ∧
      h 0 = base + S ^ 2 / (4 * (n : ℝ) ^ 2) ∧
      (∀ q : Fin k, h q.succ = base) ∧
      variance = base ∧
      lowerEnvelope h = variance

end
end MathlibPlus.Open.ResearchFormalization.R4367Claim54297
