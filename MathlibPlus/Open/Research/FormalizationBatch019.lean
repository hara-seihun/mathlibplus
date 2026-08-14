import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch019

/-- The vertices of `T(8)` are the two-element subsets of `Fin 8`. -/
def TwoSubset8 := {s : Finset (Fin 8) // s.card = 2}

private def edge01 : TwoSubset8 := ⟨{(0 : Fin 8), 1}, by decide⟩
private def edge23 : TwoSubset8 := ⟨{(2 : Fin 8), 3}, by decide⟩
private def edge45 : TwoSubset8 := ⟨{(4 : Fin 8), 5}, by decide⟩
private def edge67 : TwoSubset8 := ⟨{(6 : Fin 8), 7}, by decide⟩

/-- Membership in the four-vertex switching set `W={01,23,45,67}`. -/
def inSwitchingSet (x : TwoSubset8) : Prop :=
  x = edge01 ∨ x = edge23 ∨ x = edge45 ∨ x = edge67

/-- The Seidel-switched `T(8)` adjacency relation. -/
def switchedT8 : SimpleGraph TwoSubset8 :=
  SimpleGraph.fromRel fun x y =>
    if inSwitchingSet x = inSwitchingSet y then
      (x.1 ∩ y.1).Nonempty
    else
      ¬(x.1 ∩ y.1).Nonempty

private def deletedGraph {V : Type} (G : SimpleGraph V) (v : V) :
    SimpleGraph {x // x ≠ v} := G.comap Subtype.val

private def graphIsomorphic {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

/-- Claim 12619: `01` and `02` are in distinct automorphism orbits, witnessed by
nonisomorphic vertex-deleted graphs. -/
def claim_12619 : Prop :=
  let a : TwoSubset8 := edge01
  let b : TwoSubset8 := ⟨{(0 : Fin 8), 2}, by decide⟩
  ¬graphIsomorphic (deletedGraph switchedT8 a) (deletedGraph switchedT8 b)

/-- The path relation used in each block of the disjoint union family. -/
private def p4DirectedEdge (a b : Fin 4) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3)

/-- `mP₄`, represented by `m` blocks each carrying the path `0-1-2-3`. -/
def mP4 (m : ℕ) : SimpleGraph (Fin m × Fin 4) :=
  SimpleGraph.fromRel fun x y => x.1 = y.1 ∧ p4DirectedEdge x.2 y.2

private def swapValue (a b x : Fin 4) : Fin 4 :=
  if x = a then b else if x = b then a else x

/-- The four prescribed within-block swaps, indexed by the deleted vertex. -/
private def prescribedSwap (i x : Fin 4) : Fin 4 :=
  if i = 0 then swapValue 1 3 x
  else if i = 1 then swapValue 2 3 x
  else if i = 2 then swapValue 0 1 x
  else swapValue 0 2 x

/-- Claim 12634: in block `b`, the displayed swap is used after deleting `i`,
while all other blocks are fixed. -/
def prescribedCardMap (m : ℕ) (b : Fin m) (i : Fin 4) : Fin m × Fin 4 → Fin m × Fin 4 :=
  fun x => if x.1 = b then (x.1, prescribedSwap i x.2) else x

private def cardAutomorphism (m : ℕ) (b : Fin m) (i : Fin 4) : Prop :=
  let v : Fin m × Fin 4 := (b, i)
  Function.Bijective (prescribedCardMap m b i) ∧
    prescribedCardMap m b i v = v ∧
    ∀ x y, x ≠ v → y ≠ v →
      (mP4 m).Adj x y ↔ (mP4 m).Adj (prescribedCardMap m b i x)
        (prescribedCardMap m b i y)

/-- Claim 12635: every displayed map is an automorphism of its vertex-deleted card. -/
def claim_12635 : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (b : Fin m) (i : Fin 4), cardAutomorphism m b i

private def fullAutomorphism (m : ℕ) (b : Fin m) (i : Fin 4) : Prop :=
  ∀ x y, (mP4 m).Adj x y ↔
    (mP4 m).Adj (prescribedCardMap m b i x) (prescribedCardMap m b i y)

private def mismatchedPair (m : ℕ) (b : Fin m) (i : Fin 4) : Prop :=
  let v : Fin m × Fin 4 := (b, i)
  let pair : (Fin m × Fin 4) × (Fin m × Fin 4) :=
    match i with
    | 0 => ((b, 1), (b, 3))
    | 1 => ((b, 2), (b, 3))
    | 2 => ((b, 0), (b, 1))
    | 3 => ((b, 0), (b, 2))
  (mP4 m).Adj v pair.1 ↔ ¬(mP4 m).Adj v pair.2

/-- Claim 12636: none of the prescribed card maps is a full-graph
automorphism; the deleted vertex is adjacent to exactly one swapped vertex. -/
def claim_12636 : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (b : Fin m) (i : Fin 4),
    ¬fullAutomorphism m b i ∧ mismatchedPair m b i

end MathlibPlus.Open.ResearchFormalizationBatch019
