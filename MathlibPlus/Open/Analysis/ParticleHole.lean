import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

noncomputable section

/-- The square of the Vandermonde product on a finite set of nodes. -/
def vandermondeSq {n : ℕ} (x : Fin n → ℝ) (s : Finset (Fin n)) : ℝ :=
  ∏ i ∈ s, ∏ j ∈ s.filter (fun j => i < j), (x j - x i) ^ 2

/-- The partition function obtained from the node weights and Vandermonde square. -/
def partitionFunction {n : ℕ} (x w : Fin n → ℝ) (r : ℕ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun s => s.card = r),
    (∏ i ∈ s, w i) * vandermondeSq x s

/-- The node polynomial appearing in the dual residue factor. -/
def nodePolynomial {n : ℕ} (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (x i))

/-- The dual residue weight from the derivative of the node polynomial. -/
def dualResidueWeight {n : ℕ} (x w : Fin n → ℝ) (j : Fin n) : ℝ :=
  1 / (w j * (Polynomial.eval (x j) (Polynomial.derivative (nodePolynomial x))) ^ 2)

/--
The particle--hole complement identity: the term of `Z (n - 1)` obtained by
omitting node `j` equals `Z n` times the dual residue weight at `j`.
-/
def particleHoleComplementIdentity : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ),
    (StrictMono x ∧ (∀ i, 0 < x i) ∧ (∀ i, 0 < w i)) →
      ∀ j : Fin n,
        (∏ i ∈ (Finset.univ : Finset (Fin n)).erase j, w i) *
            vandermondeSq x ((Finset.univ : Finset (Fin n)).erase j) =
          partitionFunction x w n * dualResidueWeight x w j

end

end MathlibPlus.Open.Analysis
