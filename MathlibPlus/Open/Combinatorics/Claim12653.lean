import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch021Closure

namespace MathlibPlus.Open.Combinatorics.Claim12653

noncomputable section

abbrev SupportVertex := Fin 4
abbrev OutsideVertex := Fin 5
abbrev CrossEdge := SupportVertex × OutsideVertex
abbrev FullVertex := Sum SupportVertex OutsideVertex

private def alternatingC4Adj (u v : SupportVertex) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
  (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
  (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨
  (u = 3 ∧ v = 0) ∨ (u = 0 ∧ v = 3)

private def forcedSupportSwap : SupportVertex → SupportVertex → SupportVertex
  | 0, 1 => 3
  | 0, 3 => 1
  | 0, vertex => vertex
  | 1, 0 => 2
  | 1, 2 => 0
  | 1, vertex => vertex
  | 2, 1 => 3
  | 2, 3 => 1
  | 2, vertex => vertex
  | 3, 0 => 2
  | 3, 2 => 0
  | 3, vertex => vertex

private def supportCardEquation (deleted : SupportVertex) : Prop :=
  forcedSupportSwap deleted deleted = deleted ∧
    (∀ u : SupportVertex, u ≠ deleted →
      forcedSupportSwap deleted u ≠ deleted) ∧
    (∀ u v : SupportVertex, u ≠ deleted → v ≠ deleted →
      (alternatingC4Adj
        (forcedSupportSwap deleted u) (forcedSupportSwap deleted v) ↔
        alternatingC4Adj u v))

private def concreteOutsidePermutation : SupportVertex → Equiv.Perm OutsideVertex
  | 0 => Equiv.swap 1 2 * Equiv.swap 3 4
  | 1 => Equiv.swap 0 3 * Equiv.swap 2 4
  | 2 => Equiv.swap 0 4 * Equiv.swap 1 2
  | 3 => Equiv.swap 0 3 * Equiv.swap 1 4

private def isOutsideDoubleTransposition
    (p : Equiv.Perm OutsideVertex) : Prop :=
  ∃ a b c d : OutsideVertex,
    a ≠ b ∧ c ≠ d ∧
      Disjoint ({a, b} : Set OutsideVertex) {c, d} ∧
      p = Equiv.swap a b * Equiv.swap c d

private def supportCardPermutation (deleted : SupportVertex) :
    Equiv.Perm SupportVertex :=
  if deleted = 0 then Equiv.swap 1 3
  else if deleted = 1 then Equiv.swap 0 2
  else if deleted = 2 then Equiv.swap 1 3
  else Equiv.swap 0 2

private def fullCardMap
    (outside : SupportVertex → Equiv.Perm OutsideVertex)
    (deleted : SupportVertex) : Equiv.Perm FullVertex :=
  Equiv.sumCongr (supportCardPermutation deleted) (outside deleted)

private def isThreeTranspositionMap {α : Type*} [DecidableEq α]
    (p : Equiv.Perm α) : Prop :=
  ∃ a b c d e f : α,
    ({a, b, c, d, e, f} : Finset α).card = 6 ∧
      p = Equiv.swap a b * Equiv.swap c d * Equiv.swap e f

private def crossConstraint
    (outside : SupportVertex → Equiv.Perm OutsideVertex)
    (left right : CrossEdge) : Prop :=
  ∃ deleted : SupportVertex,
    left.1 ≠ deleted ∧
      right =
        (forcedSupportSwap deleted left.1,
          outside deleted left.2)

private def omittedImage
    (outside : SupportVertex → Equiv.Perm OutsideVertex)
    (deleted : SupportVertex) : CrossEdge :=
  (forcedSupportSwap deleted
      (MathlibPlus.Open.ResearchFormalizationBatch021Closure.omittedEdge deleted).1,
    outside deleted
      (MathlibPlus.Open.ResearchFormalizationBatch021Closure.omittedEdge deleted).2)

private def omittedRowExtends
    (outside : SupportVertex → Equiv.Perm OutsideVertex)
    (deleted : SupportVertex) : Prop :=
  Relation.EqvGen (crossConstraint outside)
    (MathlibPlus.Open.ResearchFormalizationBatch021Closure.omittedEdge deleted)
    (omittedImage outside deleted)

private def concreteActionAgreesWithReviewedRows : Prop :=
  ∀ (deleted : SupportVertex) (z : OutsideVertex),
    concreteOutsidePermutation deleted z =
      MathlibPlus.Open.ResearchFormalizationBatch021Closure.tauForRow deleted z

private def concreteClosureIsDisplayed : Prop :=
  ∀ x y : CrossEdge,
    Relation.EqvGen (crossConstraint concreteOutsidePermutation) x y ↔
      MathlibPlus.Open.ResearchFormalizationBatch021Closure.sameClosureComponent x y

/-- The forced alternating-square support maps and the displayed five-outside
vertex actions refute the proposed C4 row extension principle. -/
def directGeneralizationOfC4RowLemmaIsFalse : Prop :=
  (∀ deleted : SupportVertex, supportCardEquation deleted) ∧
    (∀ deleted : SupportVertex,
      ∀ u : SupportVertex,
        supportCardPermutation deleted u =
          forcedSupportSwap deleted u) ∧
    (∀ deleted : SupportVertex,
      isOutsideDoubleTransposition (concreteOutsidePermutation deleted)) ∧
    (∀ deleted : SupportVertex,
      isThreeTranspositionMap
        (fullCardMap concreteOutsidePermutation deleted)) ∧
    concreteActionAgreesWithReviewedRows ∧
    concreteClosureIsDisplayed ∧
    MathlibPlus.Open.ResearchFormalizationBatch021Closure.claim_12652 ∧
    (∀ deleted : SupportVertex,
      ¬ omittedRowExtends concreteOutsidePermutation deleted) ∧
    ¬ (∀ outside : SupportVertex → Equiv.Perm OutsideVertex,
      (∀ deleted : SupportVertex,
        isOutsideDoubleTransposition (outside deleted)) →
        ∃ deleted : SupportVertex, omittedRowExtends outside deleted)

end

end MathlibPlus.Open.Combinatorics.Claim12653
