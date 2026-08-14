import Mathlib

namespace MathlibPlus.Open.DecisionTrees

noncomputable section

private abbrev Cube (n : ℕ) := Fin n → Bool

private inductive Tree (n : ℕ) where
  | leaf (value : Bool)
  | query (coordinate : Fin n) (yes no : Tree n)

private def queried (i : Fin n) : Tree n → Prop
  | .leaf _ => False
  | .query j yes no => i = j ∨ queried i yes ∨ queried i no

private def legal : Tree n → Prop
  | .leaf _ => True
  | .query i yes no =>
      ¬queried i yes ∧ ¬queried i no ∧ legal yes ∧ legal no

private def eval (t : Tree n) (x : Cube n) : Bool :=
  match t with
  | .leaf b => b
  | .query i yes no => if x i then eval yes x else eval no x

private def depth : Tree n → ℕ
  | .leaf _ => 0
  | .query _ yes no => 1 + max (depth yes) (depth no)

private def booleanTreeFunction (n k : ℕ) (f : Cube n → Bool) : Prop :=
  ∃ t : Tree n, legal t ∧ depth t ≤ k ∧ ∀ x, eval t x = f x

private def treeFunctionSet (n k : ℕ) : Set ((Cube n) → ℝ) :=
  {g | ∃ f : Cube n → Bool, booleanTreeFunction n k f ∧
    ∀ x, g x = if f x then 1 else 0}

private def finiteMeanSet (n k : ℕ) : Set ((Cube n) → ℝ) :=
  {g | ∃ (m : ℕ) (w : Fin m → ℝ) (f : Fin m → Cube n → Bool),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
    (∀ i, booleanTreeFunction n k (f i)) ∧
    (∀ x, g x = ∑ i, w i * (if f i x then 1 else 0))}

def claim_17019_depth_k_tree_hull : Prop :=
  ∀ (n k : ℕ),
    convexHull ℝ (treeFunctionSet n k) = finiteMeanSet n k

end
end MathlibPlus.Open.DecisionTrees
