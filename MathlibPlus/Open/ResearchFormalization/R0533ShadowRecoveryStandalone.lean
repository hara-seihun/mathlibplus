import Mathlib

open Polynomial

namespace MathlibPlus.Open.ResearchFormalization.R0533ShadowRecoveryStandalone

noncomputable section

/-- Claim 29386: the source-bound uncapped geometric prediction at degree
`a` differs from the capped second shadow by exactly one unit for each
occurrence of length `a`, for each of the `D - 1` partner occurrences. -/
def ascendingCapRecursionCoefficientFormula_claim29386 : Prop :=
  ∀ (C : Multiset ℕ) (a : ℕ),
    (∀ ell ∈ C, 0 < ell) →
      0 < a →
      2 ≤ C.card →
      let qInteger : ℕ → Polynomial ℚ := fun ell =>
        Finset.sum (Finset.range ell) (fun i => (Polynomial.X : Polynomial ℚ) ^ i)
      let firstShadow : Multiset ℕ → Polynomial ℚ := fun M =>
        (M.map qInteger).sum
      let secondShadow : Multiset ℕ → Polynomial ℚ := fun M =>
        (1 / 2 : ℚ) •
          (firstShadow M * firstShadow M -
            (M.map (fun ell => qInteger ell * qInteger ell)).sum)
      let hybridFactor : ℕ → PowerSeries ℚ := fun ell =>
        if ell < a then
          Polynomial.toPowerSeries (qInteger ell)
        else
          (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹
      let hybridFirst : PowerSeries ℚ :=
        (C.map hybridFactor).sum
      let hybridSecond : PowerSeries ℚ :=
        (1 / 2 : ℚ) •
          (hybridFirst * hybridFirst -
            (C.map (fun ell => hybridFactor ell * hybridFactor ell)).sum)
      let B_a : ℚ := PowerSeries.coeff a hybridSecond
      let n_a : ℚ := C.count a
      ((secondShadow C).coeff a =
          B_a - ((C.card - 1 : ℕ) : ℚ) * n_a) ∧
        n_a =
          (B_a - (secondShadow C).coeff a) /
            ((C.card - 1 : ℕ) : ℚ)

/-- Claim 29388: every coefficient of the first shadow is the exact tail count
of the positive leg multiset, and equality of complete first shadows is
injective on that occurrence-sensitive carrier. -/
def firstShadowTailCounts_claim29388 : Prop :=
  (∀ (C : Multiset ℕ),
    (∀ ell ∈ C, 0 < ell) →
      let qInteger : ℕ → Polynomial ℚ := fun ell =>
        Finset.sum (Finset.range ell) (fun i => (Polynomial.X : Polynomial ℚ) ^ i)
      let firstShadow : Multiset ℕ → Polynomial ℚ := fun M =>
        (M.map qInteger).sum
      ∀ k : ℕ,
        (firstShadow C).coeff k =
          (C.countP (fun ell => k + 1 ≤ ell) : ℚ)) ∧
    (∀ C C' : Multiset ℕ,
      (∀ ell ∈ C, 0 < ell) →
      (∀ ell ∈ C', 0 < ell) →
      (let qInteger : ℕ → Polynomial ℚ := fun ell =>
          Finset.sum (Finset.range ell)
            (fun i => (Polynomial.X : Polynomial ℚ) ^ i)
       let firstShadow : Multiset ℕ → Polynomial ℚ := fun M =>
          (M.map qInteger).sum
       firstShadow C = firstShadow C') →
        C = C')

/-- Claim 29389: the first and second shadows split over the occurrence-wise
multiset sum, with the cross term equal to the product of the two first
shadows. -/
def disjointShadowDecomposition_claim29389 : Prop :=
  ∀ (A B U : Multiset ℕ),
    (∀ ell ∈ A, 0 < ell) →
    (∀ ell ∈ B, 0 < ell) →
    U = A + B →
      let qInteger : ℕ → Polynomial ℚ := fun ell =>
        Finset.sum (Finset.range ell) (fun i => (Polynomial.X : Polynomial ℚ) ^ i)
      let firstShadow : Multiset ℕ → Polynomial ℚ := fun M =>
        (M.map qInteger).sum
      let secondShadow : Multiset ℕ → Polynomial ℚ := fun M =>
        (1 / 2 : ℚ) •
          (firstShadow M * firstShadow M -
            (M.map (fun ell => qInteger ell * qInteger ell)).sum)
      firstShadow U = firstShadow A + firstShadow B ∧
        secondShadow U = secondShadow A + secondShadow B +
            firstShadow A * firstShadow B ∧
        secondShadow U - (secondShadow A + secondShadow B) =
          firstShadow A * firstShadow B

/-- Claim 29390: equal sum and product on the exact polynomial carrier recover
an unordered pair; for shadows, the global sum and the internal-shadow
subtraction provide those two elementary symmetric polynomials. -/
def quadraticShadowInversion_claim29390 : Prop :=
  (∀ P Q P' Q' : Polynomial ℚ,
    P + Q = P' + Q' →
    P * Q = P' * Q' →
    (P = P' ∧ Q = Q') ∨ (P = Q' ∧ Q = P')) ∧
  (∀ (U A B : Multiset ℕ) (I : Polynomial ℚ),
    (∀ ell ∈ U, 0 < ell) →
    (∀ ell ∈ A, 0 < ell) →
    (∀ ell ∈ B, 0 < ell) →
    U = A + B →
    I =
      (1 / 2 : ℚ) •
        (((A.map (fun ell =>
            Finset.sum (Finset.range ell)
              (fun i => (Polynomial.X : Polynomial ℚ) ^ i))).sum) *
          ((A.map (fun ell =>
            Finset.sum (Finset.range ell)
              (fun i => (Polynomial.X : Polynomial ℚ) ^ i))).sum) -
          (A.map (fun ell =>
            (Finset.sum (Finset.range ell)
              (fun i => (Polynomial.X : Polynomial ℚ) ^ i)) *
              (Finset.sum (Finset.range ell)
                (fun i => (Polynomial.X : Polynomial ℚ) ^ i)))).sum) +
        (1 / 2 : ℚ) •
          (((B.map (fun ell =>
              Finset.sum (Finset.range ell)
                (fun i => (Polynomial.X : Polynomial ℚ) ^ i))).sum) *
            ((B.map (fun ell =>
              Finset.sum (Finset.range ell)
                (fun i => (Polynomial.X : Polynomial ℚ) ^ i))).sum) -
            (B.map (fun ell =>
              (Finset.sum (Finset.range ell)
                (fun i => (Polynomial.X : Polynomial ℚ) ^ i)) *
                (Finset.sum (Finset.range ell)
                  (fun i => (Polynomial.X : Polynomial ℚ) ^ i)))).sum) →
      let qInteger : ℕ → Polynomial ℚ := fun ell =>
        Finset.sum (Finset.range ell) (fun i => (Polynomial.X : Polynomial ℚ) ^ i)
      let firstShadow : Multiset ℕ → Polynomial ℚ := fun M =>
        (M.map qInteger).sum
      let secondShadow : Multiset ℕ → Polynomial ℚ := fun M =>
        (1 / 2 : ℚ) •
          (firstShadow M * firstShadow M -
            (M.map (fun ell => qInteger ell * qInteger ell)).sum)
      firstShadow A + firstShadow B = firstShadow U ∧
        firstShadow A * firstShadow B = secondShadow U - I ∧
        (∀ A' B' : Multiset ℕ,
          (∀ ell ∈ A', 0 < ell) →
          (∀ ell ∈ B', 0 < ell) →
          U = A' + B' →
          firstShadow A' + firstShadow B' = firstShadow U →
          firstShadow A' * firstShadow B' = secondShadow U - I →
          (firstShadow A' = firstShadow A ∧
              firstShadow B' = firstShadow B) ∨
            (firstShadow A' = firstShadow B ∧
              firstShadow B' = firstShadow A)))

end

end MathlibPlus.Open.ResearchFormalization.R0533ShadowRecoveryStandalone
