import Mathlib

namespace MathlibPlus.Open.Analysis.AdmittedBatch0306D0011

open BigOperators

/-- The Poisson weight occurring in the admitted graph-norm and kernel claims. -/
noncomputable def poissonWeight (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (n.factorial : ℝ)

/-- The finite truncation of the two-term Poisson graph norm. -/
noncomputable def finiteGraphNormSquared (x : ℝ) (N : ℕ) (u : ℕ → ℂ) : ℝ :=
  Finset.sum (Finset.range (N + 1))
      (fun n => poissonWeight x n * Complex.normSq (u n)) +
    Finset.sum (Finset.range N)
      (fun n => poissonWeight x n * Complex.normSq (u (n + 1)))

/--
The exact adjacent-vertex decomposition in Claim 4407.  The finite graph norm
uses the zeroth through N-th entries in the unshifted term and the first
through N-th entries in the shifted term, as in the admitted statement.
-/
def claim4407 : Prop :=
  ∀ (x : ℝ) (N : ℕ) (u : ℕ → ℂ), 0 < x →
    finiteGraphNormSquared x N u =
      poissonWeight x 0 * Complex.normSq (u 0) +
        Finset.sum (Finset.range N) (fun n =>
          poissonWeight x (n + 1) *
            (1 + ((n + 1 : ℕ) : ℝ) / x) *
              Complex.normSq (u (n + 1)))

/-- The normalized generalized Laguerre sequence L_n^(2) from Claim 4409. -/
noncomputable def laguerrePair (t : ℝ) : ℕ → ℝ × ℝ :=
  Nat.rec (1, 3 - t) (fun n pair =>
    (pair.2,
      ((((2 * n + 5 : ℕ) : ℝ) - t) * pair.2 -
          ((n + 3 : ℕ) : ℝ) * pair.1) /
        ((n + 2 : ℕ) : ℝ)))

noncomputable def laguerreTwo (n : ℕ) (t : ℝ) : ℝ :=
  (laguerrePair t n).1

/-- The shifted feature sequence v_n from Claim 4409. -/
noncomputable def shiftedFeature : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | n + 2, t => laguerreTwo n t

/-- The finite Poisson--Laguerre Gram kernel from Claim 4410. -/
noncomputable def poissonLaguerreKernel (x : ℝ) (N : ℕ) (t s : ℝ) : ℝ :=
  Finset.sum (Finset.range N) (fun n =>
    poissonWeight x n *
      (shiftedFeature n t * shiftedFeature n s +
        shiftedFeature (n + 1) t * shiftedFeature (n + 1) s))

/--
The exact Poisson--Laguerre Gram-kernel formula, symmetry, and nonnegative
 diagonal assertion in Claim 4410.
-/
def claim4410 : Prop :=
  (∀ (x : ℝ) (N : ℕ) (t s : ℝ),
      poissonLaguerreKernel x N t s =
        Finset.sum (Finset.range N) (fun n =>
          poissonWeight x n *
            (shiftedFeature n t * shiftedFeature n s +
              shiftedFeature (n + 1) t * shiftedFeature (n + 1) s))) ∧
    (∀ (x : ℝ) (N : ℕ) (t s : ℝ),
      poissonLaguerreKernel x N t s = poissonLaguerreKernel x N s t) ∧
    (∀ (x : ℝ) (N : ℕ) (t : ℝ), 0 ≤ x →
      0 ≤ poissonLaguerreKernel x N t t)

end MathlibPlus.Open.Analysis.AdmittedBatch0306D0011
