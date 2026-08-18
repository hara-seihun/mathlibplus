import Mathlib
import MathlibPlus.Open.ResearchFormalization.BatchR0532Claims29380_29381

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0530.Claim26098

open MathlibPlus.Open.ResearchFormalization.BatchR0532

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A vertex on a repeated pendant leg: the first coordinate selects its
length, the second selects the occurrence of that length, and the third is
its position along the leg. -/
abbrev LegVertex (A : Multiset ℕ) :=
  Σ ell : {ell : ℕ // ell ∈ A.toFinset},
    Fin (A.count ell.1) × Fin ell.1

/-- The two centers, the interior trunk vertices, and the repeated pendant
leg vertices of `T(A,c,B)`. -/
abbrev DoubleSpiderVertex (A B : Multiset ℕ) (c : ℕ) :=
  Unit ⊕ (Unit ⊕ (Fin (c - 1) ⊕ (LegVertex A ⊕ LegVertex B)))

def centerA (A B : Multiset ℕ) (c : ℕ) : DoubleSpiderVertex A B c :=
  Sum.inl ()

def centerB (A B : Multiset ℕ) (c : ℕ) : DoubleSpiderVertex A B c :=
  Sum.inr (Sum.inl ())

def trunkVertex {A B : Multiset ℕ} (c : ℕ) (i : Fin (c - 1)) :
    DoubleSpiderVertex A B c :=
  Sum.inr (Sum.inr (Sum.inl i))

def legAVertex {A B : Multiset ℕ} {c : ℕ} (x : LegVertex A) :
    DoubleSpiderVertex A B c :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))

def legBVertex {A B : Multiset ℕ} {c : ℕ} (x : LegVertex B) :
    DoubleSpiderVertex A B c :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))

def trunkCoordinate {A B : Multiset ℕ} {c : ℕ}
    (v : DoubleSpiderVertex A B c) : Option ℕ :=
  match v with
  | Sum.inl _ => some 0
  | Sum.inr (Sum.inl _) => some c
  | Sum.inr (Sum.inr (Sum.inl i)) => some (i.val + 1)
  | Sum.inr (Sum.inr (Sum.inr _)) => none

def legAdjacent {A : Multiset ℕ} (x y : LegVertex A) : Prop :=
  x.1 = y.1 ∧
    x.2.1.val = y.2.1.val ∧
      (x.2.2.val + 1 = y.2.2.val ∨ y.2.2.val + 1 = x.2.2.val)

def trunkAdjacent {A B : Multiset ℕ} {c : ℕ}
    (v w : DoubleSpiderVertex A B c) : Prop :=
  ∃ i j : ℕ,
    trunkCoordinate v = some i ∧
      trunkCoordinate w = some j ∧
        (i + 1 = j ∨ j + 1 = i)

def sideAAdjacent {A B : Multiset ℕ} {c : ℕ}
    (v w : DoubleSpiderVertex A B c) : Prop :=
  (v = centerA A B c ∧
      ∃ x : LegVertex A,
        w = legAVertex x ∧ x.2.2.val = 0) ∨
    (w = centerA A B c ∧
      ∃ x : LegVertex A,
        v = legAVertex x ∧ x.2.2.val = 0) ∨
    (∃ x y : LegVertex A,
      v = legAVertex x ∧ w = legAVertex y ∧ legAdjacent x y)

def sideBAdjacent {A B : Multiset ℕ} {c : ℕ}
    (v w : DoubleSpiderVertex A B c) : Prop :=
  (v = centerB A B c ∧
      ∃ x : LegVertex B,
        w = legBVertex x ∧ x.2.2.val = 0) ∨
    (w = centerB A B c ∧
      ∃ x : LegVertex B,
        v = legBVertex x ∧ x.2.2.val = 0) ∨
    (∃ x y : LegVertex B,
      v = legBVertex x ∧ w = legBVertex y ∧ legAdjacent x y)

def doubleSpiderAdjacency {A B : Multiset ℕ} {c : ℕ}
    (v w : DoubleSpiderVertex A B c) : Prop :=
  trunkAdjacent v w ∨ sideAAdjacent v w ∨ sideBAdjacent v w

/-- The simple graph induced by the literal repeated-leg vertex carrier. -/
def doubleSpiderGraph (T : DoubleSpider) :
    SimpleGraph (DoubleSpiderVertex T.left T.right T.trunk) :=
  SimpleGraph.fromRel (doubleSpiderAdjacency (A := T.left) (B := T.right)
    (c := T.trunk))

def branchingVertices (T : DoubleSpider) :
    Set (DoubleSpiderVertex T.left T.right T.trunk) :=
  {v | 2 < (doubleSpiderGraph T).degree v}

/-- Claim 26098: the repeated-leg graph realizes the double-spider
parameterization.  Admissibility records positive legs, at least two legs on
both sides, and a positive trunk; the two centers are exactly the branching
vertices, the vertex count is the stated order, and graph isomorphism has no
parameter symmetry beyond exchanging the two sides. -/
def doubleSpiderParameterization_claim26098 : Prop :=
  ∀ T : DoubleSpider,
    admissibleDoubleSpider T →
      branchingVertices T =
          ({centerA T.left T.right T.trunk,
            centerB T.left T.right T.trunk} : Set
              (DoubleSpiderVertex T.left T.right T.trunk)) ∧
        Fintype.card (DoubleSpiderVertex T.left T.right T.trunk) =
          T.left.sum + T.right.sum + T.trunk + 1 ∧
        doubleSpiderOrder T = T.left.sum + T.right.sum + T.trunk + 1 ∧
        ∀ T' : DoubleSpider,
          admissibleDoubleSpider T' →
            Nonempty (doubleSpiderGraph T ≃g doubleSpiderGraph T') →
              sideExchangeEquivalent T T'

end

end MathlibPlus.Open.ResearchFormalization.R0530.Claim26098
