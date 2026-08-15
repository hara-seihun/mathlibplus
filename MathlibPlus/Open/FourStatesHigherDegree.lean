import Mathlib

namespace MathlibPlus.Open

/-- The polarized weight-space realization of `Sym^k (ℂ²)` from the admitted context. -/
abbrev polarizedWeightSpace (k : ℕ) := Fin (k + 1) → ℂ

/-- The mixed coefficient space in the polarized tensor basis. -/
abbrev mixedCoefficientSpace (k : ℕ) :=
  TensorProduct ℂ (polarizedWeightSpace k) (polarizedWeightSpace k)

/-- The basis vector `e_i` in the polarized weight basis. -/
def polarizedBasisVector {k : ℕ} (i : Fin (k + 1)) : polarizedWeightSpace k :=
  Pi.single i 1

/-- Reversal sends the basis index `i` to the index `k - i`. -/
def reversedIndex {k : ℕ} (i : Fin (k + 1)) : Fin (k + 1) :=
  Fin.rev i

/-- The weight attached to the basis vector `e_i`. -/
def polarizedWeight (k : ℕ) (i : Fin (k + 1)) : ℤ :=
  (k : ℤ) - 2 * (i.val : ℤ)

/-- The four selected Pauli states in the stated polarized tensor basis. -/
def pauliEqualState (k : ℕ) : mixedCoefficientSpace k :=
  ∑ i : Fin (k + 1),
    TensorProduct.tmul ℂ (polarizedBasisVector i) (polarizedBasisVector i)

def pauliOppositeState (k : ℕ) : mixedCoefficientSpace k :=
  ∑ i : Fin (k + 1),
    TensorProduct.tmul ℂ (polarizedBasisVector (reversedIndex i)) (polarizedBasisVector i)

def pauliWeightEqualState (k : ℕ) : mixedCoefficientSpace k :=
  ∑ i : Fin (k + 1),
    (polarizedWeight k i : ℂ) •
      TensorProduct.tmul ℂ (polarizedBasisVector i) (polarizedBasisVector i)

def pauliWeightOppositeState (k : ℕ) : mixedCoefficientSpace k :=
  ∑ i : Fin (k + 1),
    (-((polarizedWeight k i : ℂ))) •
      TensorProduct.tmul ℂ (polarizedBasisVector (reversedIndex i)) (polarizedBasisVector i)

/-- The diagonal support subspace of the polarized tensor grid. -/
def diagonalSupport (k : ℕ) : Submodule ℂ (mixedCoefficientSpace k) :=
  Submodule.span ℂ {
    x | ∃ i : Fin (k + 1),
      x = TensorProduct.tmul ℂ (polarizedBasisVector i) (polarizedBasisVector i)
  }

/-- The anti-diagonal support subspace of the polarized tensor grid. -/
def antiDiagonalSupport (k : ℕ) : Submodule ℂ (mixedCoefficientSpace k) :=
  Submodule.span ℂ {
    x | ∃ i : Fin (k + 1),
      x = TensorProduct.tmul ℂ (polarizedBasisVector (reversedIndex i))
        (polarizedBasisVector i)
  }

/--
At degree one the diagonal and anti-diagonal supports exhaust the mixed space;
at every degree at least two the four displayed states remain aligned while an
additional tensor-basis weight cell is off both alignments.
-/
def fourStatesDoNotExhaustHigherDegreeTargets : Prop :=
  diagonalSupport 1 ⊔ antiDiagonalSupport 1 = ⊤ ∧
    ∀ k : ℕ, 2 ≤ k →
      pauliEqualState k ∈ diagonalSupport k ∧
      pauliWeightEqualState k ∈ diagonalSupport k ∧
      pauliOppositeState k ∈ antiDiagonalSupport k ∧
      pauliWeightOppositeState k ∈ antiDiagonalSupport k ∧
      ∃ i j : Fin (k + 1),
        TensorProduct.tmul ℂ (polarizedBasisVector i) (polarizedBasisVector j) ∉
          diagonalSupport k ⊔ antiDiagonalSupport k

end MathlibPlus.Open
