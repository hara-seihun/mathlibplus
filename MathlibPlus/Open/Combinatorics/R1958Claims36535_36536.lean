import Mathlib
import MathlibPlus.Open.Combinatorics.IncidenceSunflower

namespace MathlibPlus.Open.Combinatorics.R1958

private def indexedFamily {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) : Finset (Finset α) :=
  (Finset.univ : Finset (Fin m)).image A

private def distinctUniform {α : Type*} [DecidableEq α] {m : ℕ}
    (n : ℕ) (A : Fin m → Finset α) : Prop :=
  (∀ i, (A i).card = n) ∧ Function.Injective A

private def memberSupport {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => x ∈ A i)

private def groundCoordinates {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin m)).biUnion A

private def incidencePatterns {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (groundCoordinates A).image (memberSupport A) |>.filter (fun S => S.Nonempty)

private def laminar {m : ℕ}
    (L : Finset (Finset (Fin m))) : Prop :=
  ∀ S ∈ L, ∀ T ∈ L,
    S ⊆ T ∨ T ⊆ S ∨ Disjoint S T

private def splitSupports {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α)
    (L B : Finset (Finset (Fin m))) (D : ℕ) : Prop :=
  incidencePatterns A = L ∪ B ∧
    Disjoint L B ∧
    laminar L ∧
    (∀ S ∈ B, S.card ≤ D)

private def conflictNeighbors {m : ℕ}
    (B : Finset (Finset (Fin m))) (i : Fin m) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter
    (fun j => j ≠ i ∧ ∃ S ∈ B, i ∈ S ∧ j ∈ S)

private def properConflictColoring {m r : ℕ}
    (B : Finset (Finset (Fin m))) (color : Fin m → Fin r) : Prop :=
  ∀ i j : Fin m,
    i ≠ j →
    (∃ S ∈ B, i ∈ S ∧ j ∈ S) →
    color i ≠ color j

private def restrictSupport {m r : ℕ}
    (S : Finset (Fin m)) (color : Fin m → Fin r) (c : Fin r) : Finset (Fin m) :=
  S.filter (fun i => color i = c)

private def restrictedLaminarSupports {m r : ℕ}
    (L : Finset (Finset (Fin m))) (color : Fin m → Fin r) (c : Fin r) :
    Finset (Finset (Fin m)) :=
  L.image (fun S => restrictSupport S color c)

private def completeRestrictedSupports {α : Type*} [DecidableEq α] {m r : ℕ}
    (A : Fin m → Finset α) (color : Fin m → Fin r) (c : Fin r) :
    Finset (Finset (Fin m)) :=
  (groundCoordinates A).image
    (fun x => restrictSupport (memberSupport A x) color c)

private def kSunflowerFree {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) (k : ℕ) : Prop :=
  MathlibPlus.Open.Combinatorics.isKSunflowerFree (indexedFamily A) k

/-- Claim 36535: the literal bounded-support conflict graph has the stated
per-index pattern count, maximum degree, and greedy color bound. -/
def boundedSupportConflictColoring_claim36535 : Prop :=
  ∀ {α : Type*} [DecidableEq α] (m n k D : ℕ)
    (A : Fin m → Finset α)
    (L B : Finset (Finset (Fin m))),
    distinctUniform n A →
    kSunflowerFree A k →
    splitSupports A L B D →
    (∀ i : Fin m, (B.filter (fun S => i ∈ S)).card ≤ n) ∧
      (∀ i : Fin m, (conflictNeighbors B i).card ≤ (D - 1) * n) ∧
      ∃ color : Fin m → Fin (1 + (D - 1) * n),
        properConflictColoring B color

/-- Claim 36536: every proper conflict-coloring class has laminar complete
incidence support, with the bounded and laminar restrictions explicit. -/
def colorClassCompleteIncidenceSupportLaminarity_claim36536 : Prop :=
  ∀ {α : Type*} [DecidableEq α] (m n k D : ℕ)
    (A : Fin m → Finset α)
    (L B : Finset (Finset (Fin m)))
    (color : Fin m → Fin (1 + (D - 1) * n)),
    distinctUniform n A →
    kSunflowerFree A k →
    splitSupports A L B D →
    properConflictColoring B color →
    ∀ c : Fin (1 + (D - 1) * n),
      (∀ S ∈ B,
        (restrictSupport S color c).card ≤ 1 ∧
          ((restrictSupport S color c).card = 1 →
            ∀ T ∈ L,
              restrictSupport S color c ⊆ restrictSupport T color c ∨
                restrictSupport T color c ⊆ restrictSupport S color c ∨
                Disjoint (restrictSupport S color c)
                  (restrictSupport T color c))) ∧
      laminar (restrictedLaminarSupports L color c) ∧
      laminar (completeRestrictedSupports A color c)

end MathlibPlus.Open.Combinatorics.R1958
