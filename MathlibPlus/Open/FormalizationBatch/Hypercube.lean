import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.Hypercube

private def alternatingEdge
    (n : ℕ) (X Y : Finset (Fin n)) : Prop :=
  (∃ i, i ∉ X ∧ Y = insert i X ∧ X.card % 2 = 0) ∨
    (∃ i, i ∉ Y ∧ X = insert i Y ∧ Y.card % 2 = 0)

private def cubeEdge
    (n : ℕ) (X Y : Finset (Fin n)) : Prop :=
  (∃ i, i ∉ X ∧ Y = insert i X) ∨
    (∃ i, i ∉ Y ∧ X = insert i Y)

private def fourCycleFree
    (edge : Finset (Fin n) → Finset (Fin n) → Prop) : Prop :=
  ¬ ∃ v₀ v₁ v₂ v₃ : Finset (Fin n),
      v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧
        v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
        edge v₀ v₁ ∧ edge v₁ v₂ ∧ edge v₂ v₃ ∧ edge v₃ v₀

/-- The selected alternating layers select precisely one pair of opposite
    edges in every coordinate square and contain no four-cycle. -/
def alternatingLayerGraphIsC4Free (n : ℕ) : Prop :=
  let A := alternatingEdge n
  (∀ (X : Finset (Fin n)) (i j : Fin n),
      i ≠ j → i ∉ X → j ∉ X →
        let Xi := insert i X
        let Xj := insert j X
        let Xij := insert i (insert j X)
        ((X.card % 2 = 0 ∧
            A X Xi ∧ A X Xj ∧ ¬ A Xi Xij ∧ ¬ A Xj Xij) ∨
          (X.card % 2 = 1 ∧
            ¬ A X Xi ∧ ¬ A X Xj ∧ A Xi Xij ∧ A Xj Xij))) ∧
    fourCycleFree A

/-- The complementary edge set has the two opposite edges in each coordinate
    square, meeting at the lower or upper corner according to parity. -/
def alternatingLayerGraphAndComplement (n : ℕ) : Prop :=
  let A := alternatingEdge n
  let M := fun X Y : Finset (Fin n) => cubeEdge n X Y ∧ ¬ A X Y
  ∀ (X : Finset (Fin n)) (i j : Fin n),
    i ≠ j → i ∉ X → j ∉ X →
      let Xi := insert i X
      let Xj := insert j X
      let Xij := insert i (insert j X)
      ((X.card % 2 = 0 ∧
          ¬ M X Xi ∧ ¬ M X Xj ∧ M Xi Xij ∧ M Xj Xij) ∨
        (X.card % 2 = 1 ∧
          M X Xi ∧ M X Xj ∧ ¬ M Xi Xij ∧ ¬ M Xj Xij))

end MathlibPlus.Open.FormalizationBatch.Hypercube
