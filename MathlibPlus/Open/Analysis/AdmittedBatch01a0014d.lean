import Mathlib

open scoped BigOperators
open MeasureTheory
open Set

namespace MathlibPlus.Open.Analysis

/-- Uniform averaging is the unique normalized fixed-interval `L²` minimizer. -/
def uniformLogAveragingUniqueFixedShapeMinimizer (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (a b : ℝ), a < b →
    ∀ q : ℝ → 𝕜,
      IntegrableOn q (Icc a b) volume →
      IntegrableOn (fun x => ‖q x‖ ^ 2) (Icc a b) volume →
      (∫ x in Icc a b, q x) = 1 →
      let u : ℝ → 𝕜 := fun _ => (1 : 𝕜) / (b - a)
      let energy : (ℝ → 𝕜) → ℝ := fun f => ∫ x in Icc a b, ‖f x‖ ^ 2
      energy u ≤ energy q ∧
        (energy q = energy u ↔ q =ᵐ[volume.restrict (Icc a b)] u)

/-- The minimum of the modulus of a polynomial on a circle. -/
noncomputable def polynomialCircleMinimum (D : Polynomial ℂ) (c : ℂ) (R : ℝ) : ℝ :=
  sInf {y : ℝ | ∃ z : ℂ, ‖z - c‖ = R ∧ y = ‖Polynomial.eval z D‖}

/-- The minimum of the modulus at the equally spaced samples of a circle. -/
noncomputable def polynomialSampleMinimum (D : Polynomial ℂ) (c : ℂ) (R : ℝ)
    (N : ℕ) (hN : 0 < N) : ℝ :=
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  Finset.inf' (Finset.univ : Finset (Fin N)) Finset.univ_nonempty
    (fun j : Fin N =>
    ‖Polynomial.eval
      (c + (R : ℂ) * Complex.exp
        (Complex.I * (((2 * Real.pi * (j : ℝ) / (N : ℝ)) : ℝ) : ℂ))) D‖)

/-- The finite form of the coefficient derivative bound on the disk. -/
noncomputable def polynomialCircleDerivativeBound (D : Polynomial ℂ) (c : ℂ) (R : ℝ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 D.natDegree),
    (k : ℝ) * ‖D.coeff k‖ * (‖c‖ + R) ^ (k - 1)

/-- Finite equally spaced samples give the stated lower bound on a polynomial's
boundary modulus. -/
def finiteSampledLowerBoundForPolynomialBoundaryModulus : Prop :=
  ∀ (D : Polynomial ℂ) (c : ℂ) (R : ℝ) (N : ℕ) (hR : 0 < R) (hN : 0 < N),
    polynomialCircleMinimum D c R ≥
      polynomialSampleMinimum D c R N hN -
        2 * R * Real.sin (Real.pi / (2 * (N : ℝ))) *
          polynomialCircleDerivativeBound D c R

/-- The standard upper-triangular Jordan block. -/
def jordanBlock (m : ℕ) (lambda : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if i = j then lambda else if i.val + 1 = j.val then 1 else 0

/-- Operator norm of a square complex matrix acting by multiplication on its
finite-dimensional coordinate space. -/
noncomputable def matrixOperatorNorm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  (Matrix.mulVecLin M).toContinuousLinearMap.opNorm

/-- A complex number is an eigenvalue when the characteristic determinant
vanishes. -/
def isMatrixEigenvalue {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (z : ℂ) : Prop :=
  Matrix.det (z • (1 : Matrix (Fin m) (Fin m) ℂ) - M) = 0

/-- Arbitrarily small diagonal splittings make every repeated Jordan block have
all eigenvalues distinct, while remaining close in operator norm. -/
def repeatedJordanPartitionsAreDiscontinuous : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (lambda : ℂ) (delta : ℝ), 0 < delta →
    ∃ δs : Fin m → ℂ,
      Function.Injective δs ∧
      (∀ i, ‖δs i‖ < delta) ∧
      Function.Injective (fun i => lambda + δs i) ∧
      (∀ i, isMatrixEigenvalue
        (jordanBlock m lambda + Matrix.diagonal δs) (lambda + δs i)) ∧
      matrixOperatorNorm
        ((jordanBlock m lambda + Matrix.diagonal δs) - jordanBlock m lambda) < delta

end MathlibPlus.Open.Analysis
