import Mathlib

namespace MathlibPlus.Algebra.Claim1155

open scoped BigOperators

noncomputable section

/-- The arithmetic nodes used by the source Newton array: `x_n=a+n`. -/
def node (a : ℝ) (n : ℕ) : ℝ :=
  a + (n : ℝ)

/-- The source Newton divided difference `L_m f=f[x_0,...,x_m]`, written
using the finite-difference formula at the arithmetic nodes. -/
def newtonDividedDifference (a : ℝ) (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  (Finset.sum (Finset.range (m + 1))
      (fun k =>
        (-1 : ℝ) ^ (m - k) * (Nat.choose m k : ℝ) * f (node a k))) /
    (Nat.factorial m : ℝ)

/-- The evaluation matrix in the even-power alternant. -/
def evenPowerEvaluationMatrix (a : ℝ) (d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun m j => node a m.val ^ (2 * j.val)

/-- The Newton matrix after adjoining the constant column and order-zero row. -/
def evenPowerNewtonMatrix (a : ℝ) (d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun m j =>
    newtonDividedDifference a m.val (fun x => x ^ (2 * j.val))

/-- The ordinary Vandermonde product at the arithmetic nodes. -/
def arithmeticVandermonde (a : ℝ) (d : ℕ) : ℝ :=
  Finset.prod (Finset.range (d + 1))
    (fun p => Finset.prod (Finset.Ioc p d)
      (fun q => node a q - node a p))

/-- The pairwise-sum product in the source factorization. -/
def arithmeticPairSumProduct (a : ℝ) (d : ℕ) : ℝ :=
  Finset.prod (Finset.range (d + 1))
    (fun p => Finset.prod (Finset.Ioc p d)
      (fun q => node a p + node a q))

/-- The evaluation-to-Newton change-of-basis matrix for the arithmetic nodes. -/
def evaluationToNewtonMatrix (_a : ℝ) (d : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun m n =>
    if n.val ≤ m.val then
      ((-1 : ℝ) ^ (m.val - n.val) *
          (Nat.choose m.val n.val : ℝ)) /
        (Nat.factorial m.val : ℝ)
    else 0

/-- The source identification of the Newton rows with the change-of-basis
matrix applied to evaluations. -/
def newtonChangeOfBasisRelation (a : ℝ) (d : ℕ) : Prop :=
  ∀ (f : ℝ → ℝ) (m : Fin (d + 1)),
    newtonDividedDifference a m.val f =
      ∑ n : Fin (d + 1),
        evaluationToNewtonMatrix a d m n * f (node a n.val)

/-- Claim 1155: the source-bound even-power Newton alternant is the
Vandermonde quotient and the pairwise-sum product, with the evaluation-to-
Newton determinant and its source row carrier retained explicitly. -/
def evenPowerVandermondeDet_claim1155 : Prop :=
  ∀ (a : ℝ) (d : ℕ),
    Matrix.det (evenPowerNewtonMatrix a d) =
        Matrix.det (evenPowerEvaluationMatrix a d) /
          arithmeticVandermonde a d ∧
      Matrix.det (evenPowerNewtonMatrix a d) =
        arithmeticPairSumProduct a d ∧
      Matrix.det (evaluationToNewtonMatrix a d) =
        (arithmeticVandermonde a d)⁻¹ ∧
      newtonChangeOfBasisRelation a d

/-- The quotient form of Claim 1155, with the same arithmetic-node carrier. -/
def evenPowerVandermondeQuotient_claim1155 : Prop :=
  ∀ (a : ℝ) (d : ℕ),
    Matrix.det (evenPowerEvaluationMatrix a d) /
        arithmeticVandermonde a d =
      arithmeticPairSumProduct a d

end

end MathlibPlus.Algebra.Claim1155
