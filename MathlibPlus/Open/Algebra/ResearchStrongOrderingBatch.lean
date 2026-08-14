import Mathlib

open scoped BigOperators Classical

namespace MathlibPlus.Open.Algebra

noncomputable section

private def prefixVertices {G : Type*} [AddMonoid G] (B : List G) : List G :=
  B.scanl (· + ·) 0

private def strongOrdering {G : Type*} [AddMonoid G]
    (B : List G) : Prop :=
  (B.scanl (· + ·) 0).Pairwise (· ≠ ·)

private def prefixValue {G : Type*} [AddMonoid G] (B : List G) (k : ℕ) : G :=
  (B.take k).sum

private def properPrefixTrace {G : Type*} [AddMonoid G] (B : List G) : Set G :=
  {x | ∃ k, k < B.length ∧ x = (B.take k).sum}

private def splicePieces {G : Type*} [AddCommGroup G]
    (B : List G) (u v : G) (a b : ℕ) : Fin 6 → Set G :=
  let P := prefixValue B
  let T := B.sum
  fun j =>
    if j = 0 then {0}
    else if j = 1 then {x | ∃ k, a < k ∧ k ≤ b ∧ x = P k - P a}
    else if j = 2 then {u + u - v}
    else if j = 3 then {u + u}
    else if j = 4 then {x | ∃ l, 1 ≤ l ∧ l ≤ a ∧ x = u + u + P l}
    else {x | ∃ k, b < k ∧ k < B.length ∧ x = P k - T}

private def piecesPairwiseDisjoint {G : Type*} (pieces : Fin 6 → Set G) : Prop :=
  ∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)

private def zeroOnlyInitial {G : Type*} [Zero G] (pieces : Fin 6 → Set G) : Prop :=
  ∀ j, j ≠ 0 → (0 : G) ∉ pieces j

private def simpleZeroCycle {G : Type*} [AddMonoid G] (C : List G) : Prop :=
  C.sum = 0 ∧
    (∀ i j, i < j → j < C.length →
      (C.take i).sum ≠ (C.take j).sum) ∧
    (∀ i, 0 < i → i < C.length → (C.take i).sum ≠ 0)

private def spliceList {G : Type*} [AddCommGroup G]
    (B : List G) (u v : G) (a b : ℕ) : List G :=
  (B.drop a).take (b - a) ++ [u, v] ++ B.take a ++ B.drop b

private def deleteAndRotate {G : Type*} (C : List G) (i : ℕ) : List G :=
  C.drop (i + 1) ++ C.take i

private def listAt {G : Type*} (C : List G) (i : ℕ) (hi : i < C.length) : G :=
  C.get ⟨i, hi⟩

private def maximalStrongOrdering {G : Type*} [AddMonoid G]
    (S : Finset G) (B : List G) : Prop :=
  B.Nodup ∧ (∀ x ∈ B, x ∈ S) ∧ strongOrdering B ∧
    ∀ D : List G, D.Nodup → (∀ x ∈ D, x ∈ S) →
      strongOrdering D → D.length ≤ B.length

/-- Claim 50179: the reflected-prefix splice uses all labels once and has
zero total sum. -/
def claim50179_reflectedPrefixZeroSplice : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (B : List G) (u v : G) (a b : ℕ),
    B.Nodup → strongOrdering B → u ∉ B → v ∉ B → u ≠ v →
    a < b → b ≤ B.length →
    u + v = -B.sum →
    prefixValue B a = -u → prefixValue B b = -v →
      let L := B.take a
      let M := (B.drop a).take (b - a)
      let R := B.drop b
      let C := spliceList B u v a b
      L.sum = -u ∧ R.sum = -u ∧ M.sum = u - v ∧
        C.Nodup ∧ C.sum = 0

/-- Claim 50180: the proper-prefix trace is the six displayed translated
pieces, with the stated length and injectivity of each moving piece. -/
def claim50180_sixPiecePrefixTrace : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (B : List G) (u v : G) (a b : ℕ),
    B.Nodup → strongOrdering B → a < b → b ≤ B.length →
    u + v = -B.sum → prefixValue B a = -u → prefixValue B b = -v →
      let C := spliceList B u v a b
      let pieces := splicePieces B u v a b
      properPrefixTrace C =
          pieces 0 ∪ pieces 1 ∪ pieces 2 ∪ pieces 3 ∪ pieces 4 ∪ pieces 5 ∧
        C.length = B.length + 2 ∧
        (∀ k l, a < k → k ≤ b → a < l → l ≤ b →
          prefixValue B k - prefixValue B a = prefixValue B l - prefixValue B a → k = l) ∧
        (∀ k l, 1 ≤ k → k ≤ a → 1 ≤ l → l ≤ a →
          u + u + prefixValue B k = u + u + prefixValue B l → k = l) ∧
        (∀ k l, b < k → k < B.length → b < l → l < B.length →
          prefixValue B k - B.sum = prefixValue B l - B.sum → k = l)

/-- Claim 50182: the six-piece collision criterion is equivalent to simplicity
of the zero-sum splice cycle. -/
def claim50182_sixPieceSimplicityCriterion : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (B : List G) (u v : G) (a b : ℕ),
    B.Nodup → strongOrdering B → a < b → b ≤ B.length →
    u + v = -B.sum → prefixValue B a = -u → prefixValue B b = -v →
      let C := spliceList B u v a b
      let pieces := splicePieces B u v a b
      simpleZeroCycle C ↔
        (piecesPairwiseDisjoint pieces ∧ zeroOnlyInitial pieces)

/-- Claim 50183: a simple splice cycle yields a strong ordering after deletion
of any edge and cyclic restart, including deletion of either new label. -/
def claim50183_cycleEdgeDeletionOrderings : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (B : List G) (u v : G) (a b : ℕ),
    B.Nodup → strongOrdering B → a < b → b ≤ B.length →
    u + v = -B.sum → prefixValue B a = -u → prefixValue B b = -v →
      let C := spliceList B u v a b
      simpleZeroCycle C →
        (∀ i, i < C.length → strongOrdering (deleteAndRotate C i)) ∧
        C.length = B.length + 2 ∧
        (∀ e, e ∈ B →
          ∃ i, ∃ hi : i < C.length, listAt C i hi = e ∧
            strongOrdering (deleteAndRotate C i)) ∧
        (∃ i, ∃ hi : i < C.length, listAt C i hi = u ∧
          strongOrdering (deleteAndRotate C i)) ∧
        (∃ i, ∃ hi : i < C.length, listAt C i hi = v ∧
          strongOrdering (deleteAndRotate C i))

/-- Claim 50185: maximality forbids a splice satisfying the six-piece
simplicity criterion, hence forces an explicit zero or translated-prefix
collision. -/
def claim50185_maximalOrderingCollision : Prop :=
  ∀ {G : Type*} [AddCommGroup G] (S : Finset G) (B : List G),
    maximalStrongOrdering S B →
    ∀ (u v : G) (a b : ℕ),
      u ∉ B → v ∉ B → u ≠ v → u ∈ S → v ∈ S →
      a < b → b ≤ B.length → u + v = -B.sum →
      prefixValue B a = -u → prefixValue B b = -v →
        let C := spliceList B u v a b
        let pieces := splicePieces B u v a b
        ¬ simpleZeroCycle C ∧
          (¬ piecesPairwiseDisjoint pieces ∨ ¬ zeroOnlyInitial pieces)

end

end MathlibPlus.Open.Algebra
