import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchQ0043

noncomputable section
open Classical

abbrev CapPolynomial := Polynomial ℚ
abbrev CapSeries := PowerSeries ℚ

def capFactor {n : ℕ} (A : Nat.Partition n) : CapPolynomial :=
  (A.parts.map (fun a =>
    ∑ i ∈ Finset.range (a + 1),
      (Polynomial.X : CapPolynomial) ^ i)).prod

def truncateAt (m : ℕ) (p : CapPolynomial) : CapPolynomial :=
  p.support.filter (fun i => i ≤ m) |>.sum
    (fun i => Polynomial.monomial i (p.coeff i))

def capLinearCoefficient {n : ℕ} (A : Nat.Partition n) : ℚ :=
  (capFactor A).coeff 1

def capSeries {n : ℕ} (A : Nat.Partition n) : CapSeries :=
  Polynomial.toPowerSeries (capFactor A)

def normalizedCapSeries {n : ℕ} (A : Nat.Partition n) : CapSeries :=
  (1 - (PowerSeries.X : CapSeries)) ^ A.parts.card * capSeries A

def capLogarithmicDerivative {n : ℕ} (A : Nat.Partition n) : CapSeries :=
  PowerSeries.derivative ℚ (normalizedCapSeries A) *
    PowerSeries.inv (normalizedCapSeries A)

def capPartMultiplicity {n : ℕ} (A : Nat.Partition n) (a : ℕ) : ℚ :=
  (A.parts.count a : ℚ)

def properDivisorContribution {n : ℕ} (A : Nat.Partition n) (s : ℕ) : ℚ :=
  ∑ d ∈ Finset.range (s + 1),
    if 0 < d ∧ (s + 1) % d = 0 then
      (d : ℚ) * capPartMultiplicity A (d - 1)
    else 0

def recursiveShortPartRecovery {n : ℕ} (A : Nat.Partition n) (m : ℕ) : Prop :=
  ∀ s : ℕ, s ≤ m →
    capPartMultiplicity A s =
      -(PowerSeries.coeff s (capLogarithmicDerivative A) +
        properDivisorContribution A s) / (s + 1 : ℚ)

def unrecoveredLargeParts {n : ℕ} (m : ℕ) (A : Nat.Partition n) : Multiset ℕ :=
  A.parts.filter (fun a => m < a)

def atMostOneUnrecoveredLargePart (n m : ℕ) : Prop :=
  ∀ A : Nat.Partition n,
    (unrecoveredLargeParts m A).card ≤ 1

def totalSumFixesUnrecoveredLargePart (n m : ℕ) : Prop :=
  ∀ A B : Nat.Partition n,
    A.parts.filter (fun a => a ≤ m) = B.parts.filter (fun a => a ≤ m) →
    (unrecoveredLargeParts m A).card ≤ 1 →
    (unrecoveredLargeParts m B).card ≤ 1 →
    A.parts.sum = B.parts.sum →
    unrecoveredLargeParts m A = unrecoveredLargeParts m B

/-- The cap-factor recovery assertion at the source cutoff
`m = floor (h / 2)`, including the formal logarithmic-derivative recurrence
and the unique strictly-long part left after the degree-`m` recovery. -/
def individualSpiderTruncatedCapDeterminesPartition_claim16129 : Prop :=
  ∀ (h : ℕ) (A B : Nat.Partition (h - 1)),
    let m := h / 2
    capLinearCoefficient A = (A.parts.card : ℚ) ∧
      capLinearCoefficient B = (B.parts.card : ℚ) ∧
      (truncateAt m (capFactor A) =
        truncateAt m (capFactor B) → A = B) ∧
      recursiveShortPartRecovery A m ∧
      recursiveShortPartRecovery B m ∧
      atMostOneUnrecoveredLargePart (h - 1) m ∧
      totalSumFixesUnrecoveredLargePart (h - 1) m

end

end MathlibPlus.Open.ResearchFormalization.BatchQ0043
