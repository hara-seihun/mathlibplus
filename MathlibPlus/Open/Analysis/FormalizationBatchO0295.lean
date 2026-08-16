import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0295

/-- The finite bilateral Laplace transform of a real-supported coefficient
vector. -/
noncomputable def finiteLaplaceTransform (m : ℕ) (t : Fin m → ℝ)
    (c : Fin m → ℂ) (z : ℂ) : ℂ :=
  ∑ j : Fin m, c j * Complex.exp (-z * (t j : ℂ))

/-- A complex set has an accumulation point in the usual topological sense. -/
def hasAccumulationPoint (Z : Set ℂ) : Prop :=
  ∃ z₀ : ℂ, z₀ ∈ closure (Z \ {z₀})

/-- Claim 15224's finite-support faithfulness assertion. -/
def claim15224_finite_laplace_faithfulness : Prop :=
  ∀ (m : ℕ) (t : Fin m → ℝ) (c : Fin m → ℂ) (Z : Set ℂ),
    Function.Injective t →
      hasAccumulationPoint Z →
        (∀ z : ℂ, z ∈ Z → finiteLaplaceTransform m t c z = 0) →
          c = 0

/-- The first m integer Laplace moments of a real support vector. -/
noncomputable def integerMomentMatrix (m : ℕ) (t : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun r j => Real.exp (-((r : ℕ) : ℝ) * t j)

/-- The Vandermonde matrix on the reciprocal arithmetic support. -/
noncomputable def reciprocalVandermondeMatrix (m : ℕ) (n : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.vandermonde (fun j => ((n j : ℝ)⁻¹))

/-- Arithmetic support is positive, distinct, and logarithmically represented
by the real support coordinates. -/
def arithmeticLogSupport (m : ℕ) (t : Fin m → ℝ) (n : Fin m → ℕ) : Prop :=
  (∀ j : Fin m, 0 < n j) ∧
    Function.Injective n ∧
      ∀ j : Fin m, t j = Real.log (n j : ℝ)

/-- Claim 15224's arithmetic specialization: the first m integer moments are
exactly the reciprocal-support Vandermonde system and it is invertible. -/
def claim15224_arithmetic_vandermonde : Prop :=
  ∀ (m : ℕ) (t : Fin m → ℝ) (n : Fin m → ℕ),
    arithmeticLogSupport m t n →
      integerMomentMatrix m t = reciprocalVandermondeMatrix m n ∧
        Matrix.det (reciprocalVandermondeMatrix m n) ≠ 0

/-- Claim 15224: finite bilateral Laplace faithfulness together with the
logarithmic arithmetic Vandermonde specialization. -/
def claim15224_finite_laplace_and_arithmetic_vandermonde : Prop :=
  claim15224_finite_laplace_faithfulness ∧ claim15224_arithmetic_vandermonde

end MathlibPlus.Open.Analysis.FormalizationBatchO0295
