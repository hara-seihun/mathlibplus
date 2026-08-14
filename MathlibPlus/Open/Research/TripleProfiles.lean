import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.Research.TripleProfiles

structure FiniteGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symmetric : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

 def adjacent {n : ℕ} (G : FiniteGraph n) (u v : Fin n) : Prop :=
  G.adj u v = true

 def outsideVertices {n : ℕ} (t : Fin 3 → Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∀ i, v ≠ t i)

 def neighborPattern {n : ℕ} (G : FiniteGraph n) (t : Fin 3 → Fin n)
    (v : Fin n) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => G.adj (t i) v = true)

 def outsideTable {n : ℕ} (G : FiniteGraph n) (t : Fin 3 → Fin n)
    (S : Finset (Fin 3)) : ℕ :=
  ((outsideVertices t).filter (fun v => neighborPattern G t v = S)).card

 def tableTotal (x : Finset (Fin 3) → ℕ) : ℕ :=
  ∑ S : Finset (Fin 3), x S

 def triplePattern {n : ℕ} (G : FiniteGraph n) (t : Fin 3 → Fin n) :
    Fin 3 → Fin 3 → Bool :=
  fun i j => G.adj (t i) (t j)

 def hasTripleProfile {n : ℕ} (G : FiniteGraph n)
    (A : Fin 3 → Fin 3 → Bool) (x : Finset (Fin 3) → ℕ)
    (t : Fin 3 → Fin n) : Prop :=
  Function.Injective t ∧
    (∀ i j, G.adj (t i) (t j) = A i j) ∧
    outsideTable G t = x

 def tripleProfileCount {n : ℕ} (G : FiniteGraph n)
    (A : Fin 3 → Fin 3 → Bool) (x : Finset (Fin 3) → ℕ) : ℕ :=
  (Finset.univ.filter (hasTripleProfile G A x)).card

/-- Claim 20738: the outside table is the complete ordered-triple profile. -/
def complete_ordered_triple_profile : Prop :=
  ∀ (n : ℕ) (G : FiniteGraph n) (t : Fin 3 → Fin n), Function.Injective t →
    let A := triplePattern G t
    let q := n - 3
    let x := outsideTable G t
    tableTotal x = q ∧
      tripleProfileCount G A x =
        (Finset.univ.filter (hasTripleProfile G A x)).card

 def marginD (x : Finset (Fin 3) → ℕ) (i : Fin 3) : ℕ :=
  Finset.sum (Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S)) (fun S => x S)

 def marginC (x : Finset (Fin 3) → ℕ) (i j : Fin 3) : ℕ :=
  Finset.sum (Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S ∧ j ∈ S)) (fun S => x S)

 def vertexDegree {n : ℕ} (G : FiniteGraph n) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun u => G.adj v u = true)).card

 def commonNeighborCount {n : ℕ} (G : FiniteGraph n) (u v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => G.adj u w = true ∧ G.adj v w = true)).card

 def internalDegree {n : ℕ} (G : FiniteGraph n) (t : Fin 3 → Fin n)
    (i : Fin 3) : ℕ :=
  (Finset.univ.filter (fun j => j ≠ i ∧ G.adj (t i) (t j) = true)).card

 def internalCommonNeighbors {n : ℕ} (G : FiniteGraph n) (t : Fin 3 → Fin n)
    (i j : Fin 3) : ℕ :=
  (Finset.univ.filter
    (fun k => k ≠ i ∧ k ≠ j ∧ G.adj (t i) (t k) = true ∧
      G.adj (t j) (t k) = true)).card

/-- Claim 20739: the three degree and three common-neighbor margins are exact. -/
def six_degree_common_neighbor_margins : Prop :=
  ∀ (n : ℕ) (G : FiniteGraph n) (t : Fin 3 → Fin n), Function.Injective t →
    let x := outsideTable G t
    (∀ i, vertexDegree G (t i) = marginD x i + internalDegree G t i) ∧
    (∀ i j, i ≠ j →
      commonNeighborCount G (t i) (t j) =
        marginC x i j + internalCommonNeighbors G t i j)

 def marginDInt (x : Finset (Fin 3) → ℕ) (i : Fin 3) : ℤ :=
  Finset.sum (Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S)) (fun S => (x S : ℤ))

 def marginCInt (x : Finset (Fin 3) → ℕ) (i j : Fin 3) : ℤ :=
  Finset.sum (Finset.univ.filter (fun S : Finset (Fin 3) => i ∈ S ∧ j ∈ S)) (fun S => (x S : ℤ))

 def boundaryParameter (q : ℕ) (x : Finset (Fin 3) → ℕ) : ℤ :=
  (q : ℤ) - marginDInt x 0 - marginDInt x 1 - marginDInt x 2 +
    marginCInt x 0 1 + marginCInt x 0 2 + marginCInt x 1 2

 def sameSixMargins (x y : Finset (Fin 3) → ℕ) : Prop :=
  tableTotal x = tableTotal y ∧
    (∀ i, marginD x i = marginD y i) ∧
    (∀ i j, marginC x i j = marginC y i j)

/-- Claim 20742: the empty cell determines the sole domination-boundary table. -/
def six_margin_domination_boundary_unique : Prop :=
  (∀ (q : ℕ) (x : Finset (Fin 3) → ℕ), tableTotal x = q →
    (x ∅ = 0 ↔ (x Finset.univ : ℤ) = boundaryParameter q x)) ∧
  (∀ (x y : Finset (Fin 3) → ℕ), sameSixMargins x y →
    x ∅ = 0 → y ∅ = 0 → x = y)

end MathlibPlus.Open.Research.TripleProfiles
