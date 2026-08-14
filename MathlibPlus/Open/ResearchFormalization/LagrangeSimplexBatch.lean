import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators
open MeasureTheory
noncomputable section

/-- Lagrange basis in monomial coefficient coordinates. -/
def lagrangeBasis {n : ℕ} (β : Fin n → ℝ) (i : Fin n) : Polynomial ℝ :=
  Finset.prod (Finset.univ.erase i) (fun j =>
    (Polynomial.X - Polynomial.C (β j)) *
      Polynomial.C ((β i - β j)⁻¹))

/-- Absolute Vandermonde product of the interpolation nodes. -/
def lagrangeDelta {n : ℕ} (β : Fin n → ℝ) : ℝ :=
  Finset.prod Finset.univ (fun i =>
    Finset.prod (Finset.Ioi i) (fun j => |β j - β i|))

/-- Absolute product of the interpolation nodes. -/
def lagrangeP {n : ℕ} (β : Fin n → ℝ) : ℝ :=
  Finset.prod Finset.univ (fun i => |β i|)

/-- Coefficient matrix whose rows are the Lagrange basis polynomials. -/
def lagrangeCoeffMatrix {n : ℕ} (β : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (lagrangeBasis β i).coeff (j : ℕ)

/-- Pairwise distinctness of a finite list of real nodes. -/
def pairwiseDistinctNodes {n : ℕ} (β : Fin n → ℝ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≠ j → β i ≠ β j

/-- Nonvanishing of all interpolation nodes. -/
def nonzeroNodes {n : ℕ} (β : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, β i ≠ 0

/-- Claim 25798: determinant and evaluation-product identities for the
Lagrange basis.  The displayed Salem nodes are a special case of this exact
monomial-coordinate identity. -/
def claim25798 : Prop :=
  ∀ (n : ℕ),
    0 < n →
      ∀ β : Fin n → ℝ,
        pairwiseDistinctNodes β →
          nonzeroNodes β →
            |Matrix.det (lagrangeCoeffMatrix β)| = (lagrangeDelta β)⁻¹ ∧
              Finset.prod Finset.univ (fun i =>
                |Polynomial.eval 0 (lagrangeBasis β i)|) =
                lagrangeP β ^ (n - 1) / (lagrangeDelta β) ^ 2

/-- The coefficient-space image of the weighted simplex used by the
root-sublevel construction. -/
def coefficientSimplex
    {n : ℕ} (β : Fin n → ℝ) (H : ℝ)
    (b : Polynomial ℝ) (d : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {a | ∃ y : Fin n → ℝ,
    (∀ i : Fin n, 0 ≤ y i) ∧
      (Finset.sum Finset.univ (fun i =>
          |Polynomial.eval 0 (lagrangeBasis β i)| * y i)) ≤ H / 2 ∧
        (∀ k : Fin n,
          a k = b.coeff (k : ℕ) +
            Finset.sum Finset.univ (fun i =>
              d i * y i * (lagrangeBasis β i).coeff (k : ℕ)))}

/-- Claim 25799: the exact Euclidean volume of the coefficient-space
root-sublevel simplex. -/
def claim25799 : Prop :=
  ∀ (n : ℕ),
    0 < n →
      ∀ β : Fin n → ℝ,
        pairwiseDistinctNodes β →
          nonzeroNodes β →
            ∀ (H : ℝ) (b : Polynomial ℝ) (d : Fin n → ℝ),
              0 < H →
                (b = 0 ∨ b.natDegree < n) →
                  (∀ i : Fin n, |d i| = 1) →
                    MeasureTheory.volume (coefficientSimplex β H b d) =
                      ENNReal.ofReal
                        ((H / 2) ^ n * lagrangeDelta β /
                          ((n.factorial : ℝ) * lagrangeP β ^ (n - 1)))

end
end MathlibPlus.Open.ResearchFormalization
