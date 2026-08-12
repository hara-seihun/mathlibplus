import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 34609, with the source's subset-of-the-hypercube convention made
explicit as a graph order on simple graphs over Boolean words.  `C4Free` is
written with four pairwise-distinct vertices and `matching` as maximum degree
at most one; these are the exact finite graph predicates used by the claim. -/
def alternatingLayerC4FreeExtensionClassification : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    let V := Fin n → Bool
    let weight : V → ℕ := fun x => ∑ i, if x i then 1 else 0
    let below : V → V → Prop := fun x y => ∀ i, x i ≤ y i
    let cubeRel : V → V → Prop := fun x y =>
      ∃ i : Fin n, x i ≠ y i ∧ ∀ j : Fin n, j ≠ i → x j = y j
    let alternatingRel : V → V → Prop := fun x y =>
      cubeRel x y ∧
        ((below x y ∧ Even (weight x)) ∨ (below y x ∧ Even (weight y)))
    let A : SimpleGraph V := SimpleGraph.fromRel alternatingRel
    let M : SimpleGraph V :=
      SimpleGraph.fromRel (fun x y => cubeRel x y ∧ ¬ alternatingRel x y)
    let C4Free : SimpleGraph V → Prop := fun G =>
      ∀ a b c d : V,
        a ≠ b → b ≠ c → c ≠ d → d ≠ a → a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
    let matching : SimpleGraph V → Prop := fun R =>
      ∀ v x y : V, R.Adj v x → R.Adj v y → x = y
    ∀ R : SimpleGraph V, R ≤ M →
      C4Free (A ⊔ R) ↔ matching R

end MathlibPlus.Open.GraphTheory
