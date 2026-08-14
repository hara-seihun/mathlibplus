import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

section QIntegerShadows

open Polynomial


def qInteger (a : ℕ) : Polynomial ℚ :=
  Finset.sum (Finset.range a) (fun i => X ^ i)


def firstShadow (C : Multiset ℕ) : Polynomial ℚ :=
  (C.map qInteger).sum


def secondShadow (C : Multiset ℕ) : Polynomial ℚ :=
  (1 / 2 : ℚ) •
    (firstShadow C * firstShadow C -
      (C.map (fun a => qInteger a * qInteger a)).sum)


def positiveMultiset (C : Multiset ℕ) : Prop :=
  ∀ a ∈ C, 0 < a


def multisetOfVector {D : ℕ} (C : Fin D → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset (Fin D)).1.map C


def positiveVector {D : ℕ} (C : Fin D → ℕ) : Prop :=
  ∀ i, 0 < C i

/-- Claim 29384: q-integers and the occurrence-sensitive first and second shadows. -/
def claim29384 : Prop :=
  (∀ a : ℕ, qInteger a = Finset.sum (Finset.range a) (fun i => X ^ i)) ∧
    firstShadow 0 = 0 ∧
    (∀ a C, secondShadow (a ::ₘ C) =
      qInteger a * firstShadow C + secondShadow C) ∧
    (∀ C : Multiset ℕ, positiveMultiset C →
      firstShadow C = (C.map qInteger).sum)

/-- Claim 29385: for fixed cardinality at least two, the second shadow is injective. -/
def claim29385 : Prop :=
  ∀ (D : ℕ), 2 ≤ D →
    ∀ C C' : Fin D → ℕ, positiveVector C → positiveVector C' →
      secondShadow (multisetOfVector C) = secondShadow (multisetOfVector C') →
        multisetOfVector C = multisetOfVector C'

/-- Claim 29391: an internal second shadow determines a two-side multiset grouping. -/
def claim29391 : Prop :=
  ∀ (U A B A' B' : Multiset ℕ),
    positiveMultiset U → positiveMultiset A → positiveMultiset B →
      positiveMultiset A' → positiveMultiset B' →
      A + B = U → A' + B' = U →
      secondShadow A + secondShadow B = secondShadow A' + secondShadow B' →
        (A = A' ∧ B = B') ∨ (A = B' ∧ B = A')

/-- Claim 29392: global and internal second-shadow data give the stated uniqueness. -/
def claim29392 : Prop :=
  (∀ U U' : Multiset ℕ,
      positiveMultiset U → positiveMultiset U' →
      2 ≤ U.card → U.card = U'.card →
      secondShadow U = secondShadow U' → U = U') ∧
    claim29391


end MathlibPlus.Open.ResearchFormalization
