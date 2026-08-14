import Mathlib

namespace MathlibPlus.Open.Combinatorics.UnionClosedBatch

/-- A finite family of finite subsets of a concrete finite ground of size `n`. -/
abbrev Family (n : ℕ) := Finset (Finset (Fin n))

/-- The actual ground of a family, rather than an ambient unused ground. -/
def ground {n : ℕ} (F : Family n) : Finset (Fin n) :=
  F.biUnion (fun A => A)

/-- The frequency of a coordinate in a family. -/
def frequency {n : ℕ} (F : Family n) (x : Fin n) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

/-- Union closure for a finite family. -/
def unionClosed {n : ℕ} (F : Family n) : Prop :=
  ∀ ⦃A B : Finset (Fin n)⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- An ordinary nontrivial finite counterexample to Frankl's conjecture. -/
def ordinaryCounterexample {n : ℕ} (F : Family n) : Prop :=
  F.Nonempty ∧
    (ground F).Nonempty ∧
    unionClosed F ∧
    ∀ x ∈ ground F, 2 * frequency F x < F.card

/-- The finite, ordinary formulation of Frankl's union-closed sets conjecture. -/
def franklConjecture : Prop :=
  ∀ (n : ℕ) (F : Family n),
    F.Nonempty →
    (ground F).Nonempty →
    unionClosed F →
    ∃ x ∈ ground F, 2 * frequency F x ≥ F.card

/-- `q` is the globally least actual-ground size of an ordinary counterexample. -/
def globalMinimumCounterexampleGround (q : ℕ) : Prop :=
  (∃ (n : ℕ) (F : Family n),
    ordinaryCounterexample F ∧ (ground F).card = q) ∧
    ∀ (n : ℕ) (F : Family n),
      ordinaryCounterexample F → q ≤ (ground F).card

/-- Hore's claimed `4q+1` lower bound, with `q` global rather than local. -/
def horeFourQPlusOneLowerBound (q : ℕ) : Prop :=
  globalMinimumCounterexampleGround q →
    ¬ franklConjecture →
    ∀ (n : ℕ) (F : Family n),
      ordinaryCounterexample F → 4 * q + 1 ≤ F.card

/-- A member is inclusion-minimal among members containing a chosen coordinate. -/
def inclusionMinimalContaining {n : ℕ}
    (F : Family n) (x : Fin n) (A : Finset (Fin n)) : Prop :=
  A ∈ F ∧
    x ∈ A ∧
    ∀ B, B ∈ F → x ∈ B → B ⊆ A → B = A

/-- A member is inclusion-minimal among the nonempty members of a family. -/
def inclusionMinimalNonempty {n : ℕ}
    (F : Family n) (A : Finset (Fin n)) : Prop :=
  A ∈ F ∧
    A.Nonempty ∧
    ∀ B, B ∈ F → B.Nonempty → B ⊆ A → B = A

/-- Removing a member leaves a union-closed family. -/
def removable {n : ℕ} (F : Family n) (A : Finset (Fin n)) : Prop :=
  A ∈ F ∧ unionClosed (F.erase A)

/-- A sequence of deletions, requiring the targeted minimality at every stage. -/
def xDeletionSequence {n : ℕ} (x : Fin n) :
    List (Finset (Fin n)) → Family n → Family n → Prop
  | [], F, G => G = F
  | A :: As, F, G =>
      inclusionMinimalContaining F x A ∧
        removable F A ∧
        xDeletionSequence x As (F.erase A) G

/-- A sequence of untargeted deletions through minimal nonempty members. -/
def untargetedDeletionSequence {n : ℕ} :
    List (Finset (Fin n)) → Family n → Family n → Prop
  | [], F, G => G = F
  | A :: As, F, G =>
      inclusionMinimalNonempty F A ∧
        removable F A ∧
        untargetedDeletionSequence As (F.erase A) G

/-- Sequential targeted and untargeted deletion assertions for finite union-closed families. -/
def sequentialTargetedDeletionLemma : Prop :=
  ∀ (n : ℕ) (F : Family n),
    unionClosed F →
    (∀ (x : Fin n) (A : Finset (Fin n)),
      inclusionMinimalContaining F x A → removable F A) ∧
    (∀ (x : Fin n) (r : ℕ),
      r ≤ frequency F x →
        ∃ (deletions : List (Finset (Fin n))) (G : Family n),
          deletions.length = r ∧ xDeletionSequence x deletions F G) ∧
    (∀ (A : Finset (Fin n)),
      inclusionMinimalNonempty F A → removable F A) ∧
    (∀ (r : ℕ),
      r ≤ (F.filter (fun A => A.Nonempty)).card →
        ∃ (deletions : List (Finset (Fin n))) (G : Family n),
          deletions.length = r ∧ untargetedDeletionSequence deletions F G) ∧
    (∅ ∈ F → removable F ∅)

/-- Coordinates at the counterexample's tight frequency `t`. -/
def tightCoordinates {n : ℕ} (t : ℕ) (F : Family n) : Finset (Fin n) :=
  (ground F).filter (fun x => frequency F x = t)

/-- Minimum cardinality, with actual-ground size minimized among cardinality ties. -/
def minimumActualGroundCounterexample {n : ℕ} (F : Family n) : Prop :=
  ordinaryCounterexample F ∧
    (∀ (m : ℕ) (G : Family m),
      ordinaryCounterexample G → F.card ≤ G.card) ∧
    (∀ (m : ℕ) (G : Family m),
      ordinaryCounterexample G → G.card = F.card →
        (ground F).card ≤ (ground G).card)

/-- The exact-three tight-coordinate boundary configuration used by the half-size claim. -/
def exactThreeMinimumCounterexample {n : ℕ}
    (t N : ℕ) (F : Family n) : Prop :=
  minimumActualGroundCounterexample F ∧
    F.card = 2 * t + 1 ∧
    (ground F).card = N ∧
    (tightCoordinates t F).card = 3

/-- Exact-three minimum counterexamples satisfy the stated half-size lower bound. -/
def exactThreeHalfSizeLowerBound : Prop :=
  ∀ (n : ℕ) (t N : ℕ) (F : Family n),
    exactThreeMinimumCounterexample t N F → 2 * N + 10 ≤ t

/-- The corresponding seventy-three-member floor and the stated ground-size floor. -/
def seventyThreeMemberFloor : Prop :=
  ∀ (n : ℕ) (t N : ℕ) (F : Family n),
    exactThreeMinimumCounterexample t N F → 13 ≤ N ∧ 73 ≤ F.card

end MathlibPlus.Open.Combinatorics.UnionClosedBatch
