import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0530.Claim26108

noncomputable section

private def positiveLegs (A : Multiset ℕ) : Prop :=
  ∀ ell, ell ∈ A → 0 < ell

private abbrev LegVertex (A : Multiset ℕ) :=
  Σ ell : {ell : ℕ // ell ∈ A.toFinset},
    Fin (A.count ell.1) × Fin ell.1

private abbrev DoubleSpiderVertex (A B : Multiset ℕ) (c : ℕ) :=
  Unit ⊕ (Unit ⊕ (Fin (c - 1) ⊕ (LegVertex A ⊕ LegVertex B)))

private def centerA (A B : Multiset ℕ) (c : ℕ) : DoubleSpiderVertex A B c :=
  Sum.inl ()

private def centerB (A B : Multiset ℕ) (c : ℕ) : DoubleSpiderVertex A B c :=
  Sum.inr (Sum.inl ())

private def trunkVertex (i : Fin (c - 1)) : DoubleSpiderVertex A B c :=
  Sum.inr (Sum.inr (Sum.inl i))

private def legAVertex (x : LegVertex A) : DoubleSpiderVertex A B c :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))

private def legBVertex (x : LegVertex B) : DoubleSpiderVertex A B c :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))

private def trunkCoordinate
    (v : DoubleSpiderVertex A B c) : Option ℕ :=
  match v with
  | Sum.inl _ => some 0
  | Sum.inr (Sum.inl _) => some c
  | Sum.inr (Sum.inr (Sum.inl i)) => some (i.val + 1)
  | Sum.inr (Sum.inr (Sum.inr _)) => none

private def legAdjacent {A : Multiset ℕ} (x y : LegVertex A) : Prop :=
  x.1 = y.1 ∧
    x.2.1.val = y.2.1.val ∧
      (x.2.2.val + 1 = y.2.2.val ∨ y.2.2.val + 1 = x.2.2.val)

private def trunkAdjacent
    (v w : DoubleSpiderVertex A B c) : Prop :=
  ∃ i j : ℕ,
    trunkCoordinate v = some i ∧
      trunkCoordinate w = some j ∧
        (i + 1 = j ∨ j + 1 = i)

private def sideAAdjacent
    (v w : DoubleSpiderVertex A B c) : Prop :=
  (v = centerA A B c ∧
      ∃ x : LegVertex A,
        w = legAVertex x ∧ x.2.2.val = 0) ∨
    (w = centerA A B c ∧
      ∃ x : LegVertex A,
        v = legAVertex x ∧ x.2.2.val = 0) ∨
    (∃ x y : LegVertex A,
      v = legAVertex x ∧ w = legAVertex y ∧ legAdjacent x y)

private def sideBAdjacent
    (v w : DoubleSpiderVertex A B c) : Prop :=
  (v = centerB A B c ∧
      ∃ x : LegVertex B,
        w = legBVertex x ∧ x.2.2.val = 0) ∨
    (w = centerB A B c ∧
      ∃ x : LegVertex B,
        v = legBVertex x ∧ x.2.2.val = 0) ∨
    (∃ x y : LegVertex B,
      v = legBVertex x ∧ w = legBVertex y ∧ legAdjacent x y)

private def doubleSpiderAdjacency
    (v w : DoubleSpiderVertex A B c) : Prop :=
  trunkAdjacent v w ∨ sideAAdjacent v w ∨ sideBAdjacent v w

private def connectedVertexSet
    (S : Finset (DoubleSpiderVertex A B c)) : Prop :=
  S.Nonempty ∧
    ∀ x, x ∈ S → ∀ y, y ∈ S →
      Relation.ReflTransGen
        (fun u v => doubleSpiderAdjacency u v ∧ u ∈ S ∧ v ∈ S) x y

private def componentAfterDeleting
    (deleted : Set (DoubleSpiderVertex A B c))
    (root : DoubleSpiderVertex A B c) : Set (DoubleSpiderVertex A B c) :=
  {v |
    v ∉ deleted ∧
      Relation.ReflTransGen
        (fun u w =>
          doubleSpiderAdjacency u w ∧ u ∉ deleted ∧ w ∉ deleted) root v}

private def terminalSpiderA : Set (DoubleSpiderVertex A B c) :=
  {v |
    v = centerA A B c ∨
      ∃ x : LegVertex A, v = legAVertex x}

private abbrev SuffixCutoff (A : Multiset ℕ) :=
  ∀ ell : {ell : ℕ // ell ∈ A.toFinset},
    Fin (A.count ell.1) → Fin (ell.1 + 1)

private def sideSuffixDeletedCount
    (A : Multiset ℕ) (r : SuffixCutoff A) : ℕ :=
  (Finset.univ : Finset {ell : ℕ // ell ∈ A.toFinset}).sum
    (fun ell =>
      (Finset.univ : Finset (Fin (A.count ell.1))).sum
        (fun i => ell.1 - (r ell i).val))

private def suffixDeletedSet
    (rA : SuffixCutoff A) (rB : SuffixCutoff B) :
    Set (DoubleSpiderVertex A B c) :=
  {v |
    (∃ x : LegVertex A,
      v = legAVertex x ∧
        (rA x.1 x.2.1).val ≤ x.2.2.val) ∨
    (∃ x : LegVertex B,
      v = legBVertex x ∧
        (rB x.1 x.2.1).val ≤ x.2.2.val)}

/-- Claim 26108: after orienting an unequal double spider by the smaller
side, every connected set of the giant size is either the larger-center
component after deleting the smaller center or a two-center set obtained by
cutting pendant-leg suffixes whose total size is the smaller terminal-spider
size. -/
def claim26108 : Prop :=
  ∀ (A B : Multiset ℕ) (c : ℕ),
    positiveLegs A →
      positiveLegs B →
        2 ≤ A.card →
          2 ≤ B.card →
            1 ≤ c →
              A.sum < B.sum →
                let α := A.sum
                let β := B.sum
                let h := α + 1
                let n := α + β + c + 1
                let N := β + c
                N = n - h ∧
                  N > n / 2 ∧
                    ∀ S : Finset (DoubleSpiderVertex A B c),
                      (S.card = N ∧ connectedVertexSet S) ↔
                        (((S : Set (DoubleSpiderVertex A B c)) =
                            componentAfterDeleting
                              ({centerA A B c} : Set (DoubleSpiderVertex A B c))
                              (centerB A B c) ∧
                          Set.univ \ (S : Set (DoubleSpiderVertex A B c)) =
                            terminalSpiderA) ∨
                          (centerA A B c ∈ S ∧
                            centerB A B c ∈ S ∧
                            ∃ rA : SuffixCutoff A,
                              ∃ rB : SuffixCutoff B,
                                sideSuffixDeletedCount A rA +
                                      sideSuffixDeletedCount B rB = h ∧
                                  (S : Set (DoubleSpiderVertex A B c)) =
                                    Set.univ \ suffixDeletedSet rA rB))

end

end MathlibPlus.Open.ResearchFormalization.R0530.Claim26108
