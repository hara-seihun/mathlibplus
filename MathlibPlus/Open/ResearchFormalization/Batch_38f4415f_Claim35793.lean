import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim35793

private abbrev Vertex (n : ℕ) := Fin n → ZMod 2
private abbrev EvenVertex (n : ℕ) := {x : Vertex n // ∑ i : Fin n, x i = 0}
private abbrev CubeEdge (n : ℕ) := Finset (Vertex n)
private abbrev CubeGraph (n : ℕ) := Finset (CubeEdge n)

private def toggle {n : ℕ} (x : Vertex n) (i : Fin n) : Vertex n :=
  Function.update x i (x i + 1)

private def cubeEdge {n : ℕ} (x : Vertex n) (i : Fin n) : CubeEdge n :=
  {x, toggle x i}

private def graphInCube {n : ℕ} (G : CubeGraph n) : Prop :=
  ∀ e ∈ G, ∃ x : EvenVertex n, ∃ i : Fin n,
    e = cubeEdge (x : Vertex n) i

private def selectedDirections {n : ℕ} (G : CubeGraph n)
    (x : EvenVertex n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => cubeEdge (x : Vertex n) i ∈ G)

private def hammingDistance {n : ℕ} (x y : Vertex n) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

private def c4Free {n : ℕ} (G : CubeGraph n) : Prop :=
  ∀ (x : EvenVertex n) (i j : Fin n), i ≠ j →
    ¬(cubeEdge (x : Vertex n) i ∈ G ∧
      cubeEdge (x : Vertex n) j ∈ G ∧
      cubeEdge (toggle (toggle (x : Vertex n) i) j) j ∈ G ∧
      cubeEdge (toggle (toggle (x : Vertex n) i) j) i ∈ G)

/-- C₄-freeness forces distance at least four in every fixed-outside,
    selected-support parity fiber. -/
def claim35793 : Prop :=
  ∀ (n : ℕ) (G : CubeGraph n),
    graphInCube G → c4Free G →
    ∀ (K : Finset (Fin n)) (a : Vertex n)
      (x y : EvenVertex n),
      (∀ l, l ∉ K → x.1 l = a l) →
      (∀ l, l ∉ K → y.1 l = a l) →
      K ⊆ selectedDirections G x →
      K ⊆ selectedDirections G y →
      x ≠ y →
      4 ≤ hammingDistance (x : Vertex n) (y : Vertex n)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim35793
