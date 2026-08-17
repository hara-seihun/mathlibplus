import Mathlib

open Classical
open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.R1899

noncomputable section

def primorialUpTo (z : ℕ) : ℕ :=
  ∏ q ∈ (Finset.range (z + 1)).filter Nat.Prime, q

def roughSurvivors {Q N : ℕ} (t : Fin Q) : Finset ℕ :=
  (Finset.range N).filter (fun n => Nat.Coprime (t.val + n) Q)

def roughCount {Q N : ℕ} (t : Fin Q) : ℕ :=
  (roughSurvivors (N := N) t).card

def residueCount {Q N p : ℕ} (t : Fin Q) (a : Fin p) : ℕ :=
  ((roughSurvivors (N := N) t).filter (fun n => n % p = a.val)).card

def fiberVariance {Q N : ℕ} (P : Finset ℕ) (t : Fin Q) : ℝ :=
  Finset.sum P (fun p =>
    Finset.sum Finset.univ (fun a : Fin p =>
      ((residueCount (N := N) t a : ℝ) -
        (roughCount (N := N) t : ℝ) / (p : ℝ)) ^ 2))

def varianceTotal {Q N : ℕ} (P : Finset ℕ) : Fin Q → ℝ :=
  fun t => fiberVariance (N := N) P t

def roughDensity (Q : ℕ) : ℝ :=
  (Nat.totient Q : ℝ) / (Q : ℝ)

def tailPrimeSum (P : Finset ℕ) : ℝ :=
  Finset.sum P (fun p => (1 : ℝ) / p)

def pairCorrelation {Q N : ℕ} (t : Fin Q) (h : ℕ) : ℕ :=
  ((Finset.range (N - h)).filter (fun n =>
    n ∈ roughSurvivors (N := N) t ∧
      n + h ∈ roughSurvivors (N := N) t)).card

def pairDivisorCount (P : Finset ℕ) (h : ℕ) : ℕ :=
  (P.filter (fun p => p ∣ h)).card

/-- The exact rough-sieve pair-correlation identity, retaining the positive
pair term and the negative H r(t)^2 term. -/
def claim_34782 : Prop :=
  ∀ (N z : ℕ) (P : Finset ℕ),
    let Q := primorialUpTo z
    (∀ p ∈ P, Nat.Prime p ∧ ¬ p ∣ Q) →
      ∀ t : Fin Q,
        fiberVariance (N := N) P t =
          (P.card : ℝ) * roughCount (N := N) t -
            tailPrimeSum P * (roughCount (N := N) t : ℝ) ^ 2 +
              2 * Finset.sum ((Finset.range N).filter (fun h => 0 < h))
                (fun h =>
                  ((N - h : ℕ) : ℝ) *
                    (pairDivisorCount P h : ℝ) *
                      (pairCorrelation (N := N) t h : ℝ))

/-- The averaged variance inequality and its existential base-shift
consequence. -/
def claim_34780 : Prop :=
  ∀ (N z : ℕ) (P : Finset ℕ),
    let Q := primorialUpTo z
    (∀ p ∈ P, Nat.Prime p ∧ ¬ p ∣ Q) →
      ((Q : ℝ)⁻¹ * Finset.sum Finset.univ (fun t : Fin Q =>
          fiberVariance (N := N) P t) ≤
        (N : ℝ) * roughDensity Q *
          ((P.card : ℝ) - tailPrimeSum P)) ∧
      ((Q : ℝ)⁻¹ * Finset.sum Finset.univ (fun t : Fin Q =>
          (roughCount (N := N) t : ℝ)) = (N : ℝ) * roughDensity Q) ∧
        (∃ t : Fin Q,
          fiberVariance (N := N) P t ≤
            ((P.card : ℝ) - tailPrimeSum P) * roughCount (N := N) t)

end

end MathlibPlus.Open.NumberTheory.R1899

namespace MathlibPlus.Open.Combinatorics.R1987

noncomputable section

/-- The exact trace multiplicity of a pivot intersection. -/
def traceMultiplicity {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (A T : Finset α) : ℕ :=
  (G.filter (fun B => A ∩ B = T)).card

def traceSupport {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (A : Finset α) : Finset (Finset α) :=
  G.image (fun B => A ∩ B)

def pivotMean {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (A : Finset α) : ℝ :=
  (Finset.sum G (fun B => ((A ∩ B).card : ℝ))) / (G.card : ℝ)

def traceEntropy {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (A : Finset α) : ℝ :=
  Finset.sum (traceSupport G A) (fun T =>
    let prob := (traceMultiplicity G A T : ℝ) / (G.card : ℝ)
    if prob = 0 then 0 else -prob * Real.log prob)

def pairwiseIntersecting {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) : Prop :=
  ∀ A ∈ G, ∀ B ∈ G, A ≠ B → (A ∩ B).Nonempty

def threeSunflowerFree {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) : Prop :=
  ∀ A ∈ G, ∀ B ∈ G, ∀ C ∈ G,
    A ≠ B → A ≠ C → B ≠ C →
      ¬ (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C)

/-- Entropy at a dense pivot is bounded by its expected intersection mass. -/
def claim_35069 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (r : ℕ) (A : Finset α) (ε : ℝ),
    G.Nonempty → A ∈ G →
      (∀ B ∈ G, B.card = r) →
        pairwiseIntersecting G → threeSunflowerFree G →
          0 < ε →
            pivotMean G A ≥ ε * r →
              traceEntropy G A ≤ (Real.log 2 / ε) * pivotMean G A

end

end MathlibPlus.Open.Combinatorics.R1987
