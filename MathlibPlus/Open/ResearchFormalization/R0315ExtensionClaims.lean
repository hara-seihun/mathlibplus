import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0315ExtensionClaims

abbrev Family (X : Type*) := Finset (Finset X)

def unionClosed {X : Type*} [DecidableEq X] (F : Family X) : Prop :=
  ∀ ⦃A B : Finset X⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

def frequency {X : Type*} [DecidableEq X] (F : Family X) (x : X) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

def removable {X : Type*} [DecidableEq X]
    (F : Family X) (A : Finset X) : Prop :=
  A ∈ F ∧ unionClosed (F.erase A)

def generatedByRemovables {X : Type*} [DecidableEq X]
    (F : Family X) : Prop :=
  ∀ H : Family X, unionClosed H →
    (∀ A : Finset X, removable F A → A ∈ H) →
      ∀ A ∈ F, A ∈ H

def separating {X : Type*} [DecidableEq X] (F : Family X) : Prop :=
  ∀ x y : X, x ≠ y →
    ∃ A ∈ F, (x ∈ A) ≠ (y ∈ A)

def strictCounterexample {X : Type*} [DecidableEq X]
    (F : Family X) : Prop :=
  ∀ x : X, 2 * frequency F x < F.card

def minimumCardinalityCounterexample {X : Type*} [DecidableEq X]
    (F : Family X) : Prop :=
  ∀ H : Family X, unionClosed H → strictCounterexample H →
    H.card < F.card → False

def lowerIdeal {X : Type*} [DecidableEq X]
    (F : Family X) (R : Finset X) : Family X :=
  F.filter (fun A => A ⊆ R)

def principalUpset {X : Type*} [DecidableEq X]
    (F : Family X) (R : Finset X) : Family X :=
  F.filter (fun A => R ⊆ A)

def incomparableBlock {X : Type*} [DecidableEq X]
    (F : Family X) (R : Finset X) : Family X :=
  F \ (lowerIdeal F R ∪ principalUpset F R)

def traceCell {X : Type*} [DecidableEq X]
    (F : Family X) (T A : Finset X) : Family X :=
  F.filter (fun B => B ∩ T = A)

def unionIdeal {X : Type*} [DecidableEq X]
    (F D : Family X) : Prop :=
  ∀ A ∈ D, ∀ B ∈ F, B ⊆ A → B ∈ D

def exactThreeCore {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (tight : Fin 3 → X) : Prop :=
  G.card = 53 ∧
    ∅ ∈ G ∧
    unionClosed G ∧
    Function.Injective tight ∧
    T = Finset.univ.image tight ∧
    (∀ i : Fin 3, frequency G (tight i) = 26) ∧
    (∀ x : X, x ∉ T → 2 * frequency G x < G.card) ∧
    separating G ∧
    minimumCardinalityCounterexample G ∧
    generatedByRemovables G ∧
    (∀ A ∈ G, removable G A → (A ∩ T).card ≤ 1) ∧
    (∀ x : X, ({x} : Finset X) ∉ G)

def separatorKernelWitnesses {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (tight : Fin 3 → X) : Prop :=
  ∀ i : Fin 3, ∀ x : X, x ≠ tight i →
    ∃ A : Finset X,
      A ∈ G ∧ removable G A ∧ A ∩ T = {tight i} ∧ x ∉ A

def singletonPairTraceBounds {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) : Prop :=
  ∀ A ∈ T.powerset, (A.card = 1 ∨ A.card = 2) →
    (traceCell G T A).card ≥ 3

def extensionTopLaws {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (topTight : Fin 2 → X)
    (tops : Fin 2 → Finset X) : Prop :=
  (∀ i : Fin 2,
    tops i ∉ G ∧ tops i ∩ T = {topTight i} ∧
      tops i ≠ {topTight i}) ∧
  tops 0 ∪ tops 1 ∈ G ∧
  (∀ i : Fin 2, ∀ A ∈ G,
    (A ∪ tops i ∈ G ∨ A ∪ tops i = tops i) ∧
      (¬ (A ⊆ tops i) → A ∪ tops i ∈ G))

def comparableRegionLaws {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (tops : Fin 2 → Finset X) : Prop :=
  ∀ i : Fin 2,
    let D := lowerIdeal G (tops i)
    let K := principalUpset G (tops i)
    unionIdeal G D ∧
      K = (G \ D).image (fun A => A ∪ tops i) ∧
      unionClosed (D ∪ K)

def exactExtensionCoreContext {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (tight : Fin 3 → X)
    (topTight : Fin 2 → X) (tops : Fin 2 → Finset X) : Prop :=
  exactThreeCore G T tight ∧
    (∀ i : Fin 2, ∃ j : Fin 3, topTight i = tight j) ∧
    (∀ i : Fin 2, frequency G (topTight i) = 26) ∧
    separatorKernelWitnesses G T tight ∧
    singletonPairTraceBounds G T ∧
    extensionTopLaws G T topTight tops ∧
    comparableRegionLaws G tops

/-- Claim 19732: each of the two absent extension tops has an outside
coordinate, its principal upset has size at most 23, and its incomparable
block has at least three distinct members carrying the top's tight coordinate.
The finite family, exact-three core, separator witnesses, trace cells, and
extension laws are all explicit rather than hidden in callbacks. -/
def claim19732 : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (tight : Fin 3 → X)
    (topTight : Fin 2 → X) (tops : Fin 2 → Finset X),
    exactExtensionCoreContext G T tight topTight tops →
      ∀ i : Fin 2,
        (∃ y : X, y ∈ tops i ∧ y ∉ T) ∧
        (principalUpset G (tops i)).card ≤ 23 ∧
        ((incomparableBlock G (tops i)).filter
          (fun A => topTight i ∈ A)).card ≥ 3

/-- The exact principal-upset and incomparability conclusion supplied by
Claim 19732, used as a named support premise for the compression claim. -/
def principalUpsetAndIncomparabilityBounds
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (topTight : Fin 2 → X)
    (tops : Fin 2 → Finset X) : Prop :=
  ∀ i : Fin 2,
    (∃ y : X, y ∈ tops i ∧ y ∉ T) ∧
    (principalUpset G (tops i)).card ≤ 23 ∧
    ((incomparableBlock G (tops i)).filter
      (fun A => topTight i ∈ A)).card ≥ 3

/-- Claim 19736: for each extension top, the 27 members omitting its tight
coordinate, the remaining tight-side members, and its principal upset form a
disjoint partition of the 53-member core; the remaining block has the exact
size 26 minus the principal-upset size, at least three, and adjoining the
omission block to the principal upset is union-closed of size at most 50. -/
def claim19736 : Prop :=
  ∀ {X : Type*} [Fintype X] [DecidableEq X]
    (G : Family X) (T : Finset X) (tight : Fin 3 → X)
    (topTight : Fin 2 → X) (tops : Fin 2 → Finset X),
    exactExtensionCoreContext G T tight topTight tops →
      principalUpsetAndIncomparabilityBounds G T topTight tops →
      ∀ i : Fin 2,
        let L := G.filter (fun A => topTight i ∉ A)
        let K := principalUpset G (tops i)
        let P := (G.filter (fun A => topTight i ∈ A)) \ K
        let H := L ∪ K
        L.card = 27 ∧
          G = L ∪ P ∪ K ∧
          L ∩ P = ∅ ∧ L ∩ K = ∅ ∧ P ∩ K = ∅ ∧
          P.card = 26 - K.card ∧
          P.card ≥ 3 ∧
          unionClosed H ∧ H.card ≤ 50

end MathlibPlus.Open.ResearchFormalization.R0315ExtensionClaims
