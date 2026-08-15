import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open

abbrev CubeVertex (n : ℕ) := Fin n → Bool

/-- Flip one coordinate of a Boolean cube vertex. -/
def cubeFlip {n : ℕ} (x : CubeVertex n) (i : Fin n) : CubeVertex n :=
  Function.update x i (Bool.not (x i))

def cubeAdjacent {n : ℕ} (u v : CubeVertex n) : Prop :=
  ∃ i : Fin n, u i ≠ v i ∧ ∀ j : Fin n, j ≠ i → u j = v j

def cubeEdge {n : ℕ} (u v : CubeVertex n) : Finset (CubeVertex n) := {u, v}

def cubeHostEdge {n : ℕ} (e : Finset (CubeVertex n)) : Prop :=
  ∃ u v : CubeVertex n, e = cubeEdge u v ∧ cubeAdjacent u v

def cubeSubgraph {n : ℕ} (G : Finset (Finset (CubeVertex n))) : Prop :=
  ∀ e ∈ G, cubeHostEdge e

structure CubeSquareSeed (n : ℕ) where
  i : Fin n
  j : Fin n
  x : CubeVertex n
deriving DecidableEq, Fintype

def cubeCanonicalSeed {n : ℕ} (q : CubeSquareSeed n) : Prop :=
  q.i < q.j ∧ q.x q.i = false ∧ q.x q.j = false

def cubeSquareSeeds (n : ℕ) : Finset (CubeSquareSeed n) :=
  (Finset.univ : Finset (CubeSquareSeed n)).filter cubeCanonicalSeed

def cubeSquareBoundary {n : ℕ} (q : CubeSquareSeed n) :
    Finset (Finset (CubeVertex n)) :=
  { cubeEdge q.x (cubeFlip q.x q.i),
    cubeEdge q.x (cubeFlip q.x q.j),
    cubeEdge (cubeFlip q.x q.i) (cubeFlip (cubeFlip q.x q.i) q.j),
    cubeEdge (cubeFlip q.x q.j) (cubeFlip (cubeFlip q.x q.i) q.j) }

def cubeC4Free {n : ℕ} (G : Finset (Finset (CubeVertex n))) : Prop :=
  ∀ q ∈ cubeSquareSeeds n,
    ¬ (∀ e ∈ cubeSquareBoundary q, e ∈ G)

def cubeSquareSelectedCount {n : ℕ} (G : Finset (Finset (CubeVertex n)))
    (q : CubeSquareSeed n) : ℕ :=
  (cubeSquareBoundary q).filter (fun e => e ∈ G) |>.card

def cubeHostEdgeSquareIncidence {n : ℕ} (e : Finset (CubeVertex n)) : ℕ :=
  (cubeSquareSeeds n).filter (fun q => e ∈ cubeSquareBoundary q) |>.card

/-- The square count, host-edge incidence, and C4-free square bound. -/
def formalizationClaim46653 (n : ℕ)
    (G : Finset (Finset (CubeVertex n))) : Prop :=
  cubeSubgraph G ∧ cubeC4Free G →
    (∀ q ∈ cubeSquareSeeds n, cubeSquareSelectedCount G q ≤ 3) ∧
    (cubeSquareSeeds n).card = Nat.choose n 2 * 2 ^ (n - 2) ∧
    (∀ e : Finset (CubeVertex n), cubeHostEdge e →
      cubeHostEdgeSquareIncidence e = n - 1) ∧
    (n - 1) * G.card ≤ 3 * Nat.choose n 2 * 2 ^ (n - 2)

def cubeParity {n : ℕ} (x : CubeVertex n) : Bool :=
  if (Finset.univ.filter (fun i : Fin n => x i = true)).card % 2 = 0 then
    false
  else
    true

def cubeHammingDistance {n : ℕ} (u v : CubeVertex n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card

def cubeCommonNeighbors {n : ℕ} (u v : CubeVertex n) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun w => cubeAdjacent u w ∧ cubeAdjacent v w)

def cubeSelectedAdjacent {n : ℕ}
    (G : Finset (Finset (CubeVertex n))) (u v : CubeVertex n) : Prop :=
  ∃ e ∈ G, u ∈ e ∧ v ∈ e

def cubeSelectedCommonNeighbors {n : ℕ}
    (G : Finset (Finset (CubeVertex n))) (u v : CubeVertex n) :
    Finset (CubeVertex n) :=
  Finset.univ.filter (fun w => cubeSelectedAdjacent G u w ∧ cubeSelectedAdjacent G v w)

def cubeParityClass (n : ℕ) (p : Bool) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun x => cubeParity x = p)

def cubeDegree {n : ℕ} (G : Finset (Finset (CubeVertex n)))
    (v : CubeVertex n) : ℕ :=
  (G.filter (fun e => v ∈ e)).card

/-- Same-parity distance-two common-neighbor and pair-counting statement. -/
def formalizationClaim46669 (n : ℕ)
    (G : Finset (Finset (CubeVertex n))) : Prop :=
  cubeSubgraph G ∧ cubeC4Free G →
    ∀ p : Bool,
      (∀ u v : CubeVertex n,
        cubeParity u = p → cubeParity v = p → cubeHammingDistance u v = 2 →
          (cubeCommonNeighbors u v).card = 2 ∧
          (cubeSelectedCommonNeighbors G u v).card ≤ 1) ∧
      ∑ v ∈ cubeParityClass n p, Nat.choose (cubeDegree G v) 2 ≤
        2 ^ (n - 2) * Nat.choose n 2

/-- The convexity consequence and its uniform `O(1/n)` density formulation. -/
def formalizationClaim46673 : Prop :=
  (∀ (n : ℕ) (G : Finset (Finset (CubeVertex n))),
    2 ≤ n → cubeSubgraph G → cubeC4Free G →
      let N : ℝ := (2 : ℝ) ^ (n - 1)
      let m : ℝ := (G.card : ℝ)
      m / N ≤
        (1 + Real.sqrt (1 + 2 * (n : ℝ) * (n - 1 : ℝ))) / 2) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n →
      ∀ G : Finset (Finset (CubeVertex n)),
        cubeSubgraph G → cubeC4Free G →
          (G.card : ℝ) / ((n : ℝ) * (2 : ℝ) ^ (n - 1)) ≤
            1 / Real.sqrt 2 + C / (n : ℝ))

end MathlibPlus.Open
