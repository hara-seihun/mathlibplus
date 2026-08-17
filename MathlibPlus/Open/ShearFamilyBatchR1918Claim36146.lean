import Mathlib
import MathlibPlus.Combinatorics.Claim36143
import MathlibPlus.Open.ShearFamilyBatchR1918Claim36144
import MathlibPlus.Open.ShearFamilyBatchR1918Claim36145

noncomputable section

namespace MathlibPlus.Open.ShearFamilyBatch

abbrev Claim36146Vertex (k : ℕ) := claim36144_Vertex k
abbrev Claim36146Point := claim36144_Point

 def claim36146_family (k : ℕ) (a : Fin k → ℝ) :
    Claim36146Vertex k → Claim36146Point :=
  claim36144_vertexPoint k a

def claim36146_distanceMatrix {k : ℕ}
    (X : Claim36146Vertex k → Claim36146Point) :
    Matrix (Claim36146Vertex k) (Claim36146Vertex k) ℝ :=
  fun i j => claim36144_squaredDistance (X i) (X j)

def claim36146_contactGraphFiber {k : ℕ}
    (X : Claim36146Vertex k → Claim36146Point) : Prop :=
  ∀ i j : Claim36146Vertex k,
    (i ≠ j ∧ claim36146_distanceMatrix X i j = 1) ↔
      claim36144_modelAdjacent k i j

def claim36146_minimumDistanceOne {k : ℕ}
    (X : Claim36146Vertex k → Claim36146Point) : Prop :=
  (∀ i j : Claim36146Vertex k, i ≠ j →
    1 ≤ Real.sqrt (claim36146_distanceMatrix X i j)) ∧
  ∃ i j : Claim36146Vertex k,
    i ≠ j ∧ Real.sqrt (claim36146_distanceMatrix X i j) = 1

def claim36146_diameterLength {k : ℕ}
    (X : Claim36146Vertex k → Claim36146Point) : Prop :=
  (∀ i j : Claim36146Vertex k,
    Real.sqrt (claim36146_distanceMatrix X i j) ≤
      (claim36145_Length k : ℝ)) ∧
  Real.sqrt
      (claim36146_distanceMatrix X
        (Sum.inl ⟨0, Nat.zero_lt_succ (claim36145_Length k)⟩)
        (Sum.inl (Fin.last (claim36145_Length k)))) =
    (claim36145_Length k : ℝ)

def claim36146_fixedFiber (k : ℕ) :
    Set (Claim36146Vertex k → Claim36146Point) :=
  {X |
    claim36146_contactGraphFiber X ∧
      claim36146_minimumDistanceOne X ∧
      claim36146_diameterLength X}

def claim36146_distanceFiberSpan (k : ℕ) :
    Submodule ℝ
      (Matrix (Claim36146Vertex k) (Claim36146Vertex k) ℝ) :=
  Submodule.span ℝ
    {M |
      ∃ X ∈ claim36146_fixedFiber k,
        ∃ Y ∈ claim36146_fixedFiber k,
          M = claim36146_distanceMatrix X - claim36146_distanceMatrix Y}

def claim36146_pointInner (x y : Claim36146Point) : ℝ :=
  x.1 * y.1 + x.2 * y.2

def claim36146_pointMean (k : ℕ)
    (X : Claim36146Vertex k → Claim36146Point) : Claim36146Point :=
  ((Fintype.card (Claim36146Vertex k) : ℝ)⁻¹) •
    ∑ i : Claim36146Vertex k, X i

def claim36146_centeredGramMatrix (k : ℕ)
    (X : Claim36146Vertex k → Claim36146Point) :
    Matrix (Claim36146Vertex k) (Claim36146Vertex k) ℝ :=
  fun i j =>
    claim36146_pointInner
      (X i - claim36146_pointMean k X)
      (X j - claim36146_pointMean k X)

def claim36146_centeringMatrix (k : ℕ) :
    Matrix (Claim36146Vertex k) (Claim36146Vertex k) ℝ :=
  (1 : Matrix (Claim36146Vertex k) (Claim36146Vertex k) ℝ) -
    (1 / (Fintype.card (Claim36146Vertex k) : ℝ)) •
      (fun _ _ => (1 : ℝ))

def claim36146_gramFiberSpan (k : ℕ) :
    Submodule ℝ
      (Matrix (Claim36146Vertex k) (Claim36146Vertex k) ℝ) :=
  Submodule.span ℝ
    {M |
      ∃ X ∈ claim36146_fixedFiber k,
        ∃ Y ∈ claim36146_fixedFiber k,
          M = claim36146_centeredGramMatrix k X -
            claim36146_centeredGramMatrix k Y}

def claim36146_selectedIndex (k : ℕ)
    (t : Fin k → Fin (claim36145_Length k + 1)) : Prop :=
  ∀ r : Fin k, (t r).1 = 4 * r.1 + 3

def claim36146_selectedDistances (k : ℕ)
    (t : Fin k → Fin (claim36145_Length k + 1))
    (a : Fin k → ℝ) : Fin k → ℝ :=
  fun r =>
    claim36146_distanceMatrix (claim36146_family k a)
      (Sum.inr (r, 0)) (Sum.inl (t r))

def claim36146_deltaMap (k : ℕ)
    (t : Fin k → Fin (claim36145_Length k + 1)) :
    (Fin k → ℝ) → (Fin k → ℝ) :=
  fun a => claim36146_selectedDistances k t a

/-- The selected nonedge coordinate map, its actual Jacobian, and both
physical distance-matrix and centered-Gram fiber dimensions. -/
def claim36146 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ t : Fin k → Fin (claim36145_Length k + 1),
      claim36146_selectedIndex k t ∧
      Fintype.card (Claim36146Vertex k) = 6 * k + 5 ∧
      (∀ a : Fin k → ℝ,
        claim36144_openBox k a →
          claim36146_family k a ∈ claim36146_fixedFiber k) ∧
      (∀ a : Fin k → ℝ,
        claim36144_openBox k a →
          ∀ r : Fin k,
            claim36146_deltaMap k t a r = 2 - 2 * a r) ∧
      Set.InjOn (claim36146_deltaMap k t)
        {a : Fin k → ℝ | claim36144_openBox k a} ∧
      (∀ a : Fin k → ℝ,
        claim36144_openBox k a →
          HasFDerivAt (claim36146_deltaMap k t)
            (((-2 : ℝ) •
              ContinuousLinearMap.id ℝ (Fin k → ℝ))) a ∧
          Module.finrank ℝ
            (LinearMap.range
              (((-2 : ℝ) •
                ContinuousLinearMap.id ℝ (Fin k → ℝ)).toLinearMap)) = k) ∧
      Module.finrank ℝ (claim36146_distanceFiberSpan k) ≥ k ∧
      Module.finrank ℝ (claim36146_gramFiberSpan k) ≥ k ∧
      (∀ a : Fin k → ℝ,
        claim36144_openBox k a →
          claim36146_centeredGramMatrix k (claim36146_family k a) =
            (-1 / 2 : ℝ) •
              (claim36146_centeringMatrix k *
                claim36146_distanceMatrix (claim36146_family k a) *
                claim36146_centeringMatrix k))

end MathlibPlus.Open.ShearFamilyBatch
