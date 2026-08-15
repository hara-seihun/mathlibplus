import Mathlib

namespace MathlibPlus.Open.Research.Batch_01a00468_PencilsAndLattices

noncomputable section
open scoped BigOperators
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def diagonalTestPencil (N : ℕ) (a : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) (Polynomial ℂ) :=
  Matrix.diagonal (fun j => Polynomial.X - Polynomial.C (a j))

def diagonalTestPencilAt (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => Polynomial.eval z ((diagonalTestPencil N a) i j)

def diagonalGraphEquation (a : Fin N → ℂ) (j : Fin N)
    (z : ℂ) (x y : Fin N → ℂ) : ℂ :=
  y j - (z - a j) * x j

/-- Claim 11398: the diagonal pencil graph is cut out by its coordinate equations. -/
def claim11398 : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℂ) (z : ℂ)
    (x y : Fin N → ℂ),
    ((diagonalTestPencilAt N a z).mulVec x = y) ↔
      ∀ j : Fin N, diagonalGraphEquation a j z x y = 0

def negativeRootPolynomial : Polynomial ℝ :=
  (1 + Polynomial.X) ^ 10 *
    (1 + Polynomial.C (13 : ℝ) * Polynomial.X) *
    (1 + Polynomial.C (14 : ℝ) * Polynomial.X) ^ 2

def negativeRootMultiset : Multiset ℝ :=
  Multiset.replicate 10 (-1 : ℝ) +
    ({-(1 / 13 : ℝ)} : Multiset ℝ) +
    Multiset.replicate 2 (-(1 / 14 : ℝ))

/-- Claim 11837: the explicit polynomial has exactly the stated negative roots. -/
def claim11837 : Prop :=
  negativeRootPolynomial.natDegree = 13 ∧
  negativeRootPolynomial.roots = negativeRootMultiset ∧
  (∀ z : ℝ, z ∈ negativeRootPolynomial.roots → z < 0)

def weightedTotal (w : L → ℝ) [Fintype L] : ℝ :=
  ∑ x : L, w x

def downWeight (w : L → ℝ) [Fintype L] [PartialOrder L] (r : L) : ℝ :=
  ∑ x ∈ (Finset.univ.filter (fun x => x ≤ r)), w x

def majorityHeavy (w : L → ℝ) [Fintype L] [PartialOrder L] (r : L) : Prop :=
  downWeight w r > weightedTotal w / 2

def weightedSeparatorSignature (w : L → ℝ) [Fintype L]
    [DecidableEq L] [SemilatticeSup L] [OrderTop L]
    (s : L) : Finset L :=
  Finset.univ.filter (fun r => r ≠ ⊤ ∧ majorityHeavy w r ∧ ¬ s ≤ r)

/-- Claim 19743: the weighted majority-separator signature. -/
def claim19743 : Prop :=
  ∀ (L : Type) [Fintype L] [DecidableEq L]
    [SemilatticeSup L] [OrderTop L] (w : L → ℝ),
    (∀ x : L, 0 < w x) →
    ∀ s : L,
      weightedSeparatorSignature w s =
        Finset.univ.filter
          (fun r => r ≠ ⊤ ∧
            downWeight w r > weightedTotal w / 2 ∧ ¬ s ≤ r)

end
end MathlibPlus.Open.Research.Batch_01a00468_PencilsAndLattices
