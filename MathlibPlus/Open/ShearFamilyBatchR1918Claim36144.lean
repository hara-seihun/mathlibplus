import Mathlib
import MathlibPlus.Combinatorics.Claim36143

namespace MathlibPlus.Open.ShearFamilyBatch

noncomputable section

abbrev claim36144_Point := MathlibPlus.Combinatorics.Point_claim36143
abbrev claim36144_Length (k : ℕ) := MathlibPlus.Combinatorics.hingedL_claim36143 k
abbrev claim36144_Vertex (k : ℕ) :=
  Fin (claim36144_Length k + 1) ⊕ (Fin k × Fin 2)

def claim36144_vertexPoint (k : ℕ) (a : Fin k → ℝ) :
    claim36144_Vertex k → claim36144_Point
  | Sum.inl t => MathlibPlus.Combinatorics.basePoint_claim36143 t
  | Sum.inr rb => MathlibPlus.Combinatorics.upperPoint_claim36143 a rb.1 rb.2

def claim36144_squaredDistance (x y : claim36144_Point) : ℝ :=
  (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2

def claim36144_openBox (k : ℕ) (a : Fin k → ℝ) : Prop :=
  ∀ r : Fin k, (1 : ℝ) / 10 < a r ∧ a r < 1 / 5

def claim36144_unorderedEdge {α : Type*} (i j u v : α) : Prop :=
  (i = u ∧ j = v) ∨ (i = v ∧ j = u)

def claim36144_modelAdjacent (k : ℕ)
    (i j : claim36144_Vertex k) : Prop :=
  (∃ t : Fin (claim36144_Length k),
    claim36144_unorderedEdge i j
      (Sum.inl (Fin.castSucc t)) (Sum.inl t.succ)) ∨
  (∃ r : Fin k, ∃ t : Fin (claim36144_Length k + 1),
    t.1 = 4 * r.1 + 2 ∧
      claim36144_unorderedEdge i j (Sum.inl t) (Sum.inr (r, 0))) ∨
  (∃ r : Fin k,
    claim36144_unorderedEdge i j (Sum.inr (r, 0)) (Sum.inr (r, 1))) ∨
  (∃ r : Fin k, ∃ t : Fin (claim36144_Length k + 1),
    t.1 = 4 * r.1 + 3 ∧
      claim36144_unorderedEdge i j (Sum.inr (r, 1)) (Sum.inl t))

def claim36144_unitAdjacent (k : ℕ) (a : Fin k → ℝ)
    (i j : claim36144_Vertex k) : Prop :=
  i ≠ j ∧
    claim36144_squaredDistance (claim36144_vertexPoint k a i)
      (claim36144_vertexPoint k a j) = 1

def claim36144_triangleFree (k : ℕ) (a : Fin k → ℝ) : Prop :=
  ∀ i j l : claim36144_Vertex k,
    i ≠ j → i ≠ l → j ≠ l →
      ¬ (claim36144_unitAdjacent k a i j ∧
        claim36144_unitAdjacent k a j l ∧
        claim36144_unitAdjacent k a i l)

def claim36144_scalarDistanceSeparation (a : ℝ) : Prop :=
  (1 / 10 : ℝ) < a → a < 1 / 5 →
    (∀ d : ℤ,
      ((d : ℝ) ^ 2 - 2 * a * (d : ℝ) + 1 = 1 ↔ d = 0)) ∧
    ((1 : ℝ) ^ 2 - 2 * a * (1 : ℝ) + 1 = 2 - 2 * a) ∧
    ((-1 : ℝ) ^ 2 - 2 * a * (-1 : ℝ) + 1 = 2 + 2 * a) ∧
    (2 - 2 * a > 8 / 5) ∧ (2 + 2 * a > 1) ∧
    (∀ d : ℤ, 2 ≤ Int.natAbs d →
      1 < (d : ℝ) ^ 2 - 2 * a * (d : ℝ) + 1)

def claim36144_distanceFormulas (k : ℕ) (a : Fin k → ℝ) : Prop :=
  (∀ r : Fin k, claim36144_scalarDistanceSeparation (a r)) ∧
  (∀ r : Fin k, ∀ t : Fin (claim36144_Length k + 1),
    let d := (t.1 : ℝ) - (4 * r.1 + 2 : ℕ)
    claim36144_squaredDistance
        (MathlibPlus.Combinatorics.basePoint_claim36143 t)
        (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 0) =
      d ^ 2 - 2 * a r * d + 1) ∧
  (∀ r : Fin k, ∀ t : Fin (claim36144_Length k + 1),
    let d := (t.1 : ℝ) - (4 * r.1 + 3 : ℕ)
    claim36144_squaredDistance
        (MathlibPlus.Combinatorics.basePoint_claim36143 t)
        (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 1) =
      d ^ 2 - 2 * a r * d + 1) ∧
  (∀ r : Fin k,
    claim36144_squaredDistance
        (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 0)
        (MathlibPlus.Combinatorics.upperPoint_claim36143 a r 1) = 1)

def fixedContactGraphTriangleFree : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
    ∀ (a : Fin k → ℝ), claim36144_openBox k a →
      claim36144_distanceFormulas k a ∧
      (∀ i j : claim36144_Vertex k,
        claim36144_unitAdjacent k a i j ↔
          claim36144_modelAdjacent k i j) ∧
      (∀ b : Fin k → ℝ, claim36144_openBox k b →
        ∀ i j : claim36144_Vertex k,
          claim36144_unitAdjacent k a i j ↔
            claim36144_unitAdjacent k b i j) ∧
      claim36144_triangleFree k a

end

end MathlibPlus.Open.ShearFamilyBatch
