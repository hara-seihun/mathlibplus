import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics

/-- The number of members of a finite family containing a coordinate. -/
def incidenceDegree {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (x : α) : ℕ :=
  (𝓕.filter (fun A => x ∈ A)).card

/-- The ground coordinates occurring in a finite family. -/
def groundCoordinates {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Finset α :=
  𝓕.biUnion (fun A => A)

/-- Uniformity of a family of finite sets. -/
def isNUniform {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ A ∈ 𝓕, A.card = n

/-- Absence of k distinct members with one common pairwise-intersection core. -/
def isKSunflowerFree {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (k : ℕ) : Prop :=
  ¬ ∃ (A : Fin k → Finset α) (C : Finset α),
      (∀ i, A i ∈ 𝓕) ∧
      (∀ i j : Fin k, i ≠ j → A i ≠ A j) ∧
      (∀ i, C ⊆ A i) ∧
      (∀ i j : Fin k, i ≠ j → A i ∩ A j = C)

/-- The two-sided incidence-degree restriction called Record 1 in the claims. -/
def incidenceRecordOne {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (m n k D E : ℕ) : Prop :=
  𝓕.card = m ∧
    isNUniform 𝓕 n ∧
    isKSunflowerFree 𝓕 k ∧
    3 ≤ k ∧
    1 ≤ D ∧
    0 ≤ E ∧
    ∀ x ∈ groundCoordinates 𝓕,
      incidenceDegree 𝓕 x ≤ D ∨ m - incidenceDegree 𝓕 x ≤ E

/-- Members omitted by a fixed coordinate. -/
def omittedDegree {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (x : α) : ℕ :=
  (𝓕.filter (fun A => x ∉ A)).card

/-- Coordinates whose incidence degree is heavy. -/
def heavyCoordinates {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (D : ℕ) : Finset α :=
  (groundCoordinates 𝓕).filter (fun x => D < incidenceDegree 𝓕 x)

/-- The exact trace of a member on a coordinate set. -/
def traceOn {α : Type*} [DecidableEq α]
    (H A : Finset α) : Finset α :=
  A ∩ H

/-- Number of traces realized by the members of a family on H. -/
def realizedTraceCount {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (H : Finset α) : ℕ :=
  (𝓕.image (fun A => traceOn H A)).card

/-- Total missing incidences of a family on H. -/
def totalMissingIncidences {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (H : Finset α) : ℕ :=
  Finset.sum 𝓕 (fun A => (H \ A).card)

/-- The two cases in the sharpened k=3 coefficient, with no value at D=0. -/
def sharpenedBValue (D n b : ℕ) : Prop :=
  (D = 1 ∧ b = 2) ∨
    (2 ≤ D ∧ b = min (2 * D * n) (3 * (D - 1) * n + 3))

/-- Eventual quadratic growth of the displayed k=3 bound for fixed D and E. -/
def sharpenedBoundIsQuadratic (D E : ℕ) : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ b : ℕ,
      sharpenedBValue D n b ∧
        max (2 * E) (b * (2 * E * n + 1)) ≤ C * n ^ 2

/-- Claim 34755: the restricted two-sided incidence-degree class. -/
def claim34755 {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (m n k D E : ℕ) : Prop :=
  incidenceRecordOne 𝓕 m n k D E

/-- Claim 34756: the missing-incidence and exact-trace bound. -/
def claim34756 {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (m n k D E : ℕ) : Prop :=
  incidenceRecordOne 𝓕 m n k D E ∧
    (let H := heavyCoordinates 𝓕 D
     let q := realizedTraceCount 𝓕 H
     (∀ x ∈ H, omittedDegree 𝓕 x ≤ E) ∧
       q - 1 ≤ totalMissingIncidences 𝓕 H ∧
       totalMissingIncidences 𝓕 H =
         Finset.sum H (fun x => m - incidenceDegree 𝓕 x) ∧
       (m > 2 * E →
         (∀ x ∈ H, m / 2 < incidenceDegree 𝓕 x) ∧
           (Finset.sum (groundCoordinates 𝓕) (fun x => incidenceDegree 𝓕 x) = m * n) ∧
           H.card < 2 * n ∧
           q ≤ 2 * E * n + 1))

/-- Claim 34757: the general fixed-k polynomial sunflower bound. -/
def claim34757 {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (m n k D E : ℕ) : Prop :=
  incidenceRecordOne 𝓕 m n k D E ∧
    m ≤ max (2 * E) ((k - 1) * D * n * (2 * E * n + 1))

/-- Claim 34758: the sharpened k=3 bound and its quadratic growth. -/
def claim34758 {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (m n k D E : ℕ) : Prop :=
  k = 3 ∧
    incidenceRecordOne 𝓕 m n k D E ∧
    (∃ b : ℕ,
      sharpenedBValue D n b ∧
        m ≤ max (2 * E) (b * (2 * E * n + 1))) ∧
    sharpenedBoundIsQuadratic D E

end MathlibPlus.Open.Combinatorics
