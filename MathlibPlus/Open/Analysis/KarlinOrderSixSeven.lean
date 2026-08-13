import Mathlib

namespace MathlibPlus.Open.Analysis.Karlin

/-- Claim 887: the signed order-six consecutive-derivative determinant is
nonnegative for every nonzero real polynomial of degree at most six whose
complex roots are real and nonpositive. -/
def degreeAtMostSixOrderSixPositivity_claim887 : Prop :=
  ∀ (f : Polynomial ℝ),
    f ≠ 0 →
    f.natDegree ≤ 6 →
    (∀ z : ℂ,
      Polynomial.IsRoot (Polynomial.map (algebraMap ℝ ℂ) f) z →
        z.im = 0 ∧ z.re ≤ 0) →
    ∀ (x : ℝ), 0 ≤ x →
      (-1 : ℝ) ^ 15 *
        Matrix.det (fun i j : Fin 6 =>
          ((Polynomial.derivative^[i.1 + j.1]) f).eval x) ≥ 0

/-- Claim 888: for a product of at most six nonnegative reciprocal-root
factors, the order-six Toeplitz derivative determinant is nonnegative, and
its zero/strict-positive cases are exactly determined by the number of
positive factors. -/
def productDeterminantExactPositivityClassification_claim888 : Prop :=
  ∀ (N : ℕ), N ≤ 6 →
    ∀ (α : Fin N → ℝ),
      (∀ i, 0 ≤ α i) →
      let G : Polynomial ℝ :=
        ∏ i : Fin N, (1 + Polynomial.C (α i) * Polynomial.X)
      let D₆ : ℝ :=
        Matrix.det (fun i j : Fin 6 =>
          ((Polynomial.derivative^[5 + j.1 - i.1]) G).eval 0)
      D₆ ≥ 0 ∧
        (D₆ = 0 ↔
          ∃ S : Finset (Fin N), S.card ≤ 4 ∧
            ∀ i, (0 < α i ↔ i ∈ S)) ∧
        (0 < D₆ ↔
          ∃ S : Finset (Fin N), 5 ≤ S.card ∧
            ∀ i, (0 < α i ↔ i ∈ S))

/-- Claim 893: if at most four reciprocal-root parameters are positive, the
order-six product determinant vanishes. -/
def supportAtMostFourVanishing_claim893 : Prop :=
  ∀ (N : ℕ) (α : Fin N → ℝ),
    (∀ i, 0 ≤ α i) →
    (∃ S : Finset (Fin N), S.card ≤ 4 ∧
      ∀ i, (0 < α i ↔ i ∈ S)) →
    let G : Polynomial ℝ :=
      ∏ i : Fin N, (1 + Polynomial.C (α i) * Polynomial.X)
    Matrix.det (fun i j : Fin 6 =>
      ((Polynomial.derivative^[5 + j.1 - i.1]) G).eval 0) = 0

/-- Claim 897: the displayed seven positive, pairwise-distinct reciprocal
parameters give a positive-leading degree-seven polynomial with exactly
simple strictly negative roots and a negative signed order-six determinant. -/
def simpleStrictlyNegativeRootDegreeSevenCounterexample_claim897 : Prop :=
  let q : ℝ := 10000000
  let α : Fin 7 → ℝ := ![
    (53 * q - 3) / q,
    (53 * q - 1) / q,
    (53 * q + 1) / q,
    (53 * q + 3) / q,
    (q - 2) / q,
    1,
    (q + 2) / q]
  (∀ i, 0 < α i) ∧
    Function.Injective α ∧
    let G : Polynomial ℝ :=
      ∏ i : Fin 7, (1 + Polynomial.C (α i) * Polynomial.X)
    G.natDegree = 7 ∧
      0 < G.leadingCoeff ∧
      (∀ z : ℂ,
        Polynomial.IsRoot (Polynomial.map (algebraMap ℝ ℂ) G) z ↔
          ∃ i, z = -((α i : ℝ) : ℂ)⁻¹) ∧
      Matrix.det (fun i j : Fin 6 =>
        ((Polynomial.derivative^[5 + j.1 - i.1]) G).eval 0) < 0

/-- Claim 898: degree six is the largest degree for universal signed
order-six positivity, while degree seven already fails with simple strictly
negative roots. -/
def sharpDegreeThreshold_claim898 : Prop :=
  (∀ (f : Polynomial ℝ),
    f ≠ 0 →
    f.natDegree ≤ 6 →
    (∀ z : ℂ,
      Polynomial.IsRoot (Polynomial.map (algebraMap ℝ ℂ) f) z →
        z.im = 0 ∧ z.re ≤ 0) →
    ∀ (x : ℝ), 0 ≤ x →
      (-1 : ℝ) ^ 15 *
        Matrix.det (fun i j : Fin 6 =>
          ((Polynomial.derivative^[i.1 + j.1]) f).eval x) ≥ 0) ∧
    simpleStrictlyNegativeRootDegreeSevenCounterexample_claim897

end MathlibPlus.Open.Analysis.Karlin
