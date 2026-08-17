import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim35795

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

private def hammingDistance {n : ℕ} (x y : Vertex n) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

private def c4Free {n : ℕ} (G : CubeGraph n) : Prop :=
  ∀ (x : EvenVertex n) (i j : Fin n), i ≠ j →
    ¬(cubeEdge (x : Vertex n) i ∈ G ∧
      cubeEdge (x : Vertex n) j ∈ G ∧
      cubeEdge (toggle (toggle (x : Vertex n) i) j) j ∈ G ∧
      cubeEdge (toggle (toggle (x : Vertex n) i) j) i ∈ G)

private def evenCodeDistanceFour {k : ℕ}
    (S : Finset (EvenVertex k)) : Prop :=
  ∀ ⦃x y : EvenVertex k⦄, x ∈ S → y ∈ S → x ≠ y →
    4 ≤ hammingDistance (x : Vertex k) (y : Vertex k)

private noncomputable def AEven (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : Finset (EvenVertex k) =>
    evenCodeDistanceFour S)).sup Finset.card

private def alpha (k : ℕ) : ℝ :=
  (AEven k : ℝ) / (2 : ℝ) ^ (k - 1)

private def uniformExpectation {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

private def degreeExpectation {n : ℕ} (G : CubeGraph n) : ℝ :=
  uniformExpectation (fun x : EvenVertex n => (selectedDegree G x : ℝ))

/-- C₄-freeness and the exact even-code capacity give the complete
    degree-binomial moment bound, in both expectation and cleared forms. -/
def claim35795 : Prop :=
  ∀ (n : ℕ) (G : CubeGraph n),
    graphInCube G → c4Free G →
    ∀ k : ℕ, k ≤ n →
      (uniformExpectation (fun x : EvenVertex n =>
          (Nat.choose (selectedDegree G x) k : ℝ)) ≤
        alpha k * (Nat.choose n k : ℝ)) ∧
      (∑ x : EvenVertex n, Nat.choose (selectedDegree G x) k ≤
        AEven k * 2 ^ (n - k) * Nat.choose n k)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim35795
