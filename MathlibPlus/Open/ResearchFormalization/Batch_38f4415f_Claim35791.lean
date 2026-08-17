import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim35791

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

private def selectedDegree {n : ℕ} (G : CubeGraph n)
    (x : EvenVertex n) : ℕ :=
  (selectedDirections G x).card

private def uniformExpectation {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

private def degreeExpectation {n : ℕ} (G : CubeGraph n) : ℝ :=
  uniformExpectation (fun x : EvenVertex n => (selectedDegree G x : ℝ))

private def directionProbability {n : ℕ} (G : CubeGraph n)
    (i : Fin n) : ℝ :=
  uniformExpectation (fun x : EvenVertex n =>
    if i ∈ selectedDirections G x then 1 else 0)

/-- The unique-even-endpoint edge encoding gives the exact degree and
    direction-expectation identities. -/
def claim35791 : Prop :=
  ∀ (n : ℕ) (G : CubeGraph n),
    graphInCube G →
      G.card = ∑ x : EvenVertex n, selectedDegree G x ∧
      (∑ i : Fin n, directionProbability G i = degreeExpectation G) ∧
      (G.card : ℝ) = (2 : ℝ) ^ (n - 1) * degreeExpectation G

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim35791
