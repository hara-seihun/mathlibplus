import Mathlib

noncomputable section

/-!
# Degree-seven order-seven Karlin positivity

Proof-free statement carrier for admitted claim 962.  The source notation
`K₇(f;x)` is made explicit as the signed consecutive derivative determinant;
the complex-root condition is retained rather than replaced by a factorization
or a stronger polynomial hypothesis.
-/

namespace MathlibPlus.Open.Analysis.Karlin

/-- Claim 962: a positive-leading polynomial of degree at most seven whose
complex roots are all real and nonpositive has nonnegative order-seven Karlin
determinant on the nonnegative real axis. -/
def degreeAtMostSevenOrderSevenPositivity_claim962 : Prop :=
  let K7 : Polynomial ℝ → ℝ → ℝ := fun f x =>
    (-1 : ℝ) ^ 21 *
      Matrix.det (fun i j : Fin 7 =>
        ((Polynomial.derivative^[i.1 + j.1]) f).eval x)
  ∀ f : Polynomial ℝ,
    0 < f.leadingCoeff →
    f.natDegree ≤ 7 →
    (∀ z : ℂ,
      Polynomial.IsRoot (Polynomial.map (algebraMap ℝ ℂ) f) z →
        z.im = 0 ∧ z.re ≤ 0) →
    ∀ x : ℝ, 0 ≤ x → 0 ≤ K7 f x

end MathlibPlus.Open.Analysis.Karlin
