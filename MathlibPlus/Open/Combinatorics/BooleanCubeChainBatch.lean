import Mathlib

namespace MathlibPlus.Open.Combinatorics

abbrev CubeVertex (n : ℕ) := Finset (Fin n)
abbrev CubeEdge (n : ℕ) := CubeVertex n × CubeVertex n

/-- A selected edge is oriented from a subset to the result of adding one
coordinate. -/
def selectedEdge {n : ℕ} (G : Finset (CubeEdge n))
    (U V : CubeVertex n) : Prop := (U, V) ∈ G

def completeCoordinateSquareFree {n : ℕ} (G : Finset (CubeEdge n)) : Prop :=
  ∀ (U : CubeVertex n) (x y : Fin n),
    x ∉ U → y ∉ U → x ≠ y →
    ¬ (selectedEdge G U (insert x U) ∧
      selectedEdge G U (insert y U) ∧
      selectedEdge G (insert x U) (insert y (insert x U)) ∧
      selectedEdge G (insert y U) (insert x (insert y U)))

/-- An enumeration of the coordinates in an interval. -/
abbrev IntervalChain (n k : ℕ) (A B : CubeVertex n) :=
  {π : Fin k → Fin n //
    Function.Injective π ∧ ∀ i, π i ∈ B \ A}

def chainPrefix {n k : ℕ} {A B : CubeVertex n}
    (π : IntervalChain n k A B) (r : ℕ) : CubeVertex n :=
  A ∪ ((Finset.univ.filter (fun i : Fin k => i.val < r)).image π.1)

abbrev chainSelected {n k : ℕ} {A B : CubeVertex n}
    (G : Finset (CubeEdge n)) (π : IntervalChain n k A B) : Prop :=
  ∀ i : Fin k,
    selectedEdge G (chainPrefix π i.val) (chainPrefix π (i.val + 1))

noncomputable def maximalChains {n k : ℕ} (G : Finset (CubeEdge n))
    (A B : CubeVertex n) : Finset (IntervalChain n k A B) := by
  classical
  exact Finset.univ.filter (chainSelected G)

/-- Claim 45859: the adjacent-transposition bound for every Boolean interval. -/
def claim45859_adjacent_transposition_chain_bound : Prop :=
  ∀ (n k : ℕ) (G : Finset (CubeEdge n))
    (A B : CubeVertex n),
    A ⊆ B → (B \ A).card = k → 2 ≤ k →
    completeCoordinateSquareFree G →
    (maximalChains (k := k) G A B).card ≤ Nat.factorial k / 2

/-- Claim 45860: the same bound in the probability language for a uniformly
random maximal interval chain. -/
def claim45860_random_chain_probability : Prop :=
  ∀ (n k : ℕ) (G : Finset (CubeEdge n))
    (A B : CubeVertex n),
    A ⊆ B → (B \ A).card = k → 2 ≤ k →
    completeCoordinateSquareFree G →
    ((maximalChains (k := k) G A B).card : ℚ) /
      (Nat.factorial k : ℚ) ≤ (1 : ℚ) / 2

end MathlibPlus.Open.Combinatorics
