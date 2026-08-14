import Mathlib

noncomputable section

/-! Proof-free statement carriers for admitted Karlin claims 963, 973, and 974. -/

namespace MathlibPlus.Open.Analysis.Karlin

/-- Claim 963: the order-seven product determinant is nonnegative for at most
seven nonnegative factors, with equality exactly at positive support at most
five. -/
def productDeterminantExactPositivityClassification_claim963 : Prop :=
  ∀ (N : ℕ), N ≤ 7 → ∀ α : Fin N → ℝ,
    (∀ i, 0 ≤ α i) →
    let G : Polynomial ℝ :=
      ∏ i : Fin N, (1 + Polynomial.C (α i) * Polynomial.X)
    let D : ℝ :=
      Matrix.det (fun i j : Fin 7 =>
        ((Polynomial.derivative^[6 + j.1 - i.1]) G).eval 0)
    D ≥ 0 ∧
      (D = 0 ↔ ∃ S : Finset (Fin N), S.card ≤ 5 ∧
        ∀ i, (0 < α i ↔ i ∈ S)) ∧
      (0 < D ↔ ∃ S : Finset (Fin N), 6 ≤ S.card ∧
        ∀ i, (0 < α i ↔ i ∈ S))

/-- Claim 973: the explicit eight-factor positive rational witness has simple
strictly negative roots and negative order-seven determinant. -/
def simpleStrictlyNegativeRootDegreeEightCounterexample_claim973 : Prop :=
  let q : ℝ := 10000000
  let α : Fin 8 → ℝ := ![
    (13 * q - 4) / q, (13 * q - 2) / q, 13,
    (13 * q + 2) / q, (13 * q + 4) / q,
    (q - 2) / q, 1, (q + 2) / q]
  (∀ i, 0 < α i) ∧ Function.Injective α ∧
    let G : Polynomial ℝ :=
      ∏ i : Fin 8, (1 + Polynomial.C (α i) * Polynomial.X)
    0 < G.leadingCoeff ∧ G.natDegree = 8 ∧
      (∀ z : ℂ,
        Polynomial.IsRoot (Polynomial.map (algebraMap ℝ ℂ) G) z ↔
          ∃ i, z = -((α i : ℝ) : ℂ)⁻¹) ∧
      Matrix.det (fun i j : Fin 7 =>
        ((Polynomial.derivative^[6 + j.1 - i.1]) G).eval 0) < 0

/-- Claim 974: degree eight is the sharp first degree for order-seven failure,
even with simple strictly negative roots. -/
def sharpDegreeThresholdOrderSeven_claim974 : Prop :=
  (∀ (f : Polynomial ℝ),
    0 < f.leadingCoeff →
    f.natDegree ≤ 7 →
    (∀ z : ℂ,
      Polynomial.IsRoot (Polynomial.map (algebraMap ℝ ℂ) f) z →
        z.im = 0 ∧ z.re ≤ 0) →
    ∀ x : ℝ, 0 ≤ x →
      0 ≤ (-1 : ℝ) ^ 21 *
        Matrix.det (fun i j : Fin 7 =>
          ((Polynomial.derivative^[i.1 + j.1]) f).eval x)) ∧
    simpleStrictlyNegativeRootDegreeEightCounterexample_claim973

end MathlibPlus.Open.Analysis.Karlin
