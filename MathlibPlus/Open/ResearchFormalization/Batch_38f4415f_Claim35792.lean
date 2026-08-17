import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim35792

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

private def supportSet {n : ℕ} (G : CubeGraph n)
    (K : Finset (Fin n)) : Set (EvenVertex n) :=
  {x | K ⊆ selectedDirections G x}

private abbrev CoordinateFiber (n : ℕ) (K : Finset (Fin n))
    (a : Vertex n) :=
  {x : EvenVertex n // ∀ i, i ∉ K → x.1 i = a i}

/-- Fixing coordinates outside K leaves exactly one parity class of the
    binary K-cube inside the selected even-vertex carrier. -/
def claim35792 : Prop :=
  ∀ (n k : ℕ) (G : CubeGraph n) (K : Finset (Fin n))
    (a : Vertex n),
    graphInCube G → K.card = k →
    let T_K := supportSet G K
    T_K = {x : EvenVertex n | K ⊆ selectedDirections G x} ∧
    ∃ b : ZMod 2,
      (∀ x : CoordinateFiber n K a,
        (∑ i : K, (x.1 : Vertex n) i.1) = b) ∧
      (∀ v : K → ZMod 2, (∑ i, v i = b) →
        ∃! x : CoordinateFiber n K a,
          ∀ i : K, (x.1 : Vertex n) i.1 = v i)

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.Claim35792
