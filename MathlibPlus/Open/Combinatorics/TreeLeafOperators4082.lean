import MathlibPlus.Open.Combinatorics.TreeLeafOperators4071_4074

namespace MathlibPlus.Open.Combinatorics.TreeLeafOperators4082

open scoped BigOperators
open MathlibPlus.Open.Combinatorics.TreeLeafOperators

noncomputable section

/-- The squared coefficient norm on the exact rational tree space. -/
def treeNormSq4082 {n : ℕ} (x : TreeSpace n) : ℚ :=
  ∑ T : TreeClass n, (x T) ^ 2

/-- Claim 4082: on the exact finite tree-isomorphism-class spaces and the
reviewed leaf graft/prune operators, the up/down norm identity, its singular
value lower-bound form, injectivity/surjectivity consequences, and adjoint
pairing are retained together. -/
def claim4082_upDownNormIdentity : Prop :=
  ∀ (n : ℕ) (_hn : 0 < n),
    (∀ x : TreeSpace n,
      treeNormSq4082 (leafGraftingOperator n x) =
        treeNormSq4082 (leafPruningOperator n x) +
          (n : ℚ) * treeNormSq4082 x) ∧
    (∀ x : TreeSpace n,
      (n : ℚ) * treeNormSq4082 x ≤
        treeNormSq4082 (leafGraftingOperator n x)) ∧
    Function.Injective (leafGraftingOperator n) ∧
    Function.Surjective (leafPruningOperator (n + 1)) ∧
    (∀ x : TreeSpace n, ∀ y : TreeSpace (n + 1),
      treePairing (leafGraftingOperator n x) y =
        treePairing x (leafPruningOperator (n + 1) y))

end

end MathlibPlus.Open.Combinatorics.TreeLeafOperators4082
