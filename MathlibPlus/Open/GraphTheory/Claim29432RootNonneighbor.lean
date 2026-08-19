import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.Claim29432

/-- The labeled order-12 representative of `K₅ ⊔ K₇`. -/
private def kFiveUnionKSevenAdj (i j : Fin 12) : Prop :=
  i ≠ j ∧
    ((i.1 < 5 ∧ j.1 < 5) ∨
      (5 ≤ i.1 ∧ 5 ≤ j.1))

/-- The labeled order-12 representative of bridged `K₆ ⊔ K₆`. -/
private def bridgedKSixUnionKSixAdj (i j : Fin 12) : Prop :=
  i ≠ j ∧
    ((i.1 < 6 ∧ j.1 < 6) ∨
      (6 ≤ i.1 ∧ 6 ≤ j.1) ∨
      (i.1 = 0 ∧ j.1 = 6) ∨
      (i.1 = 6 ∧ j.1 = 0))

/-- A graph has the specified labeled shape up to relabeling. -/
private def hasShape (H : SimpleGraph (Fin 12))
    (shape : Fin 12 → Fin 12 → Prop) : Prop :=
  ∃ e : Fin 12 ≃ Fin 12,
    ∀ i j : Fin 12, H.Adj i j ↔ shape (e i) (e j)

/-- Balanced-block signs are the `F₂` labels on distinct pair vertices. -/
private def balancedSigning (s : Fin 12 → Fin 12 → ZMod 2) : Prop :=
  ∀ i j : Fin 12, i ≠ j → s i j = s j i

/-- The zero-mismatch root-nonneighbor block polarity: a nonbalanced block is
full, while a balanced block has the signed two-endpoint adjacency law. -/
private def rootNonneighborAdj (H : SimpleGraph (Fin 12))
    (s : Fin 12 → Fin 12 → ZMod 2)
    (x y : Fin 12 × ZMod 2) : Prop :=
  x.1 ≠ y.1 ∧
    (¬ H.Adj x.1 y.1 ∨
      (H.Adj x.1 y.1 ∧ x.2 + y.2 = s x.1 y.1))

/-- Five selected endpoints from five distinct transposition pairs. -/
private def fivePairTransversal
    (S : Finset (Fin 12 × ZMod 2)) : Prop :=
  S.card = 5 ∧ (S.image Prod.fst).card = 5

private def cliqueFiveTransversal (H : SimpleGraph (Fin 12))
    (s : Fin 12 → Fin 12 → ZMod 2) : Prop :=
  ∃ S : Finset (Fin 12 × ZMod 2),
    fivePairTransversal S ∧
      ∀ ⦃x y : Fin 12 × ZMod 2⦄,
        x ∈ S → y ∈ S → x ≠ y → rootNonneighborAdj H s x y

private def independentFiveTransversal (H : SimpleGraph (Fin 12))
    (s : Fin 12 → Fin 12 → ZMod 2) : Prop :=
  ∃ S : Finset (Fin 12 × ZMod 2),
    fivePairTransversal S ∧
      ∀ ⦃x y : Fin 12 × ZMod 2⦄,
        x ∈ S → y ∈ S → x ≠ y → ¬ rootNonneighborAdj H s x y

/-- The signing avoids both forbidden five-transversals. -/
private def avoidsBothTransversals (H : SimpleGraph (Fin 12))
    (s : Fin 12 → Fin 12 → ZMod 2) : Prop :=
  ¬ cliqueFiveTransversal H s ∧ ¬ independentFiveTransversal H s

/-- Claim 29432: neither of the two order-12 extremal shapes admits
root-nonneighbor balanced-block signs avoiding both clique-five and
independent-five transversals.  The polarity, signed endpoint law, and
five-distinct-pair carrier are all explicit. -/
def neitherExtremalShapeRootNonneighborSigning_claim29432 : Prop :=
  (∀ H : SimpleGraph (Fin 12),
    hasShape H kFiveUnionKSevenAdj →
      ∀ s : Fin 12 → Fin 12 → ZMod 2,
        balancedSigning s → ¬ avoidsBothTransversals H s) ∧
  (∀ H : SimpleGraph (Fin 12),
    hasShape H bridgedKSixUnionKSixAdj →
      ∀ s : Fin 12 → Fin 12 → ZMod 2,
        balancedSigning s → ¬ avoidsBothTransversals H s)

end MathlibPlus.Open.GraphTheory.Claim29432
