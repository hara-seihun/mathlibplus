import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch9937

noncomputable section

/-- The arithmetic sum attached to a real source. -/
def arithmeticSum (q : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑' n : ℕ, q (((n + 1 : ℕ) : ℝ) * v)

/-- The logarithmically conjugated arithmetic sum. -/
def bulkKernel (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t / 2) * arithmeticSum q (Real.exp t)

/-- The even bulk kernel used by the literal Mellin/Fourier transform. -/
def evenBulkKernel (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (bulkKernel q t + bulkKernel q (-t))

/-- The literal transform on the complex spectral axis. -/
def literalTransform (L : ℝ) (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in (-L)..L,
    (evenBulkKernel q t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))

/--
Surgery by an everywhere-positive central polynomial preserves the complete real
 double-zero set of the literal transform.
-/
def surgeryPreservesCompleteRealDiscriminant : Prop :=
  ∀ (q qtilde : ℝ → ℝ) (L : ℝ) (Q : Polynomial ℝ),
    (∀ z : ℂ,
      literalTransform L qtilde z =
        Polynomial.eval₂ (algebraMap ℝ ℂ) (z ^ 2) Q * literalTransform L q z) →
    (∀ x : ℝ, 0 < Q.eval (x ^ 2)) →
    {x : ℝ | literalTransform L qtilde (x : ℂ) = 0 ∧
      deriv (literalTransform L qtilde) (x : ℂ) = 0} =
    {x : ℝ | literalTransform L q (x : ℂ) = 0 ∧
      deriv (literalTransform L q) (x : ℂ) = 0}

end

end MathlibPlus.Open.ResearchFormalization.Batch9937
