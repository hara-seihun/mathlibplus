import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch11355

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.K0021K0031K0035

noncomputable section

/-- Claim 6929: the rational edge-image margin polynomial is exactly
positive precisely when the edge image has norm greater than the positive
rational margin. -/
def exactBoundaryMarginPolynomial_claim6929
    (A B : Polynomial ℚ) (η : ℚ) : Prop :=
  0 < η ∧
    let q : Polynomial ℚ :=
      A ^ 2 + B ^ 2 - Polynomial.C (η ^ 2)
    let Aℝ : Polynomial ℝ := Polynomial.map (algebraMap ℚ ℝ) A
    let Bℝ : Polynomial ℝ := Polynomial.map (algebraMap ℚ ℝ) B
    let qℝ : Polynomial ℝ := Polynomial.map (algebraMap ℚ ℝ) q
    ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      (qℝ.eval t > 0 ↔
        ‖((Aℝ.eval t : ℝ) : ℂ) + Complex.I * ((Bℝ.eval t : ℝ) : ℂ)‖ > (η : ℝ))

/-- Claim 6992: the p=2 witness is tied to the source definitions of
`c_24(p)`, the adjoint eigenvalue, Ramanujan tau, and `rho_p`; the displayed
finite decimal is recorded as incompatible with the exact fraction rather
than silently replacing either source datum. -/
def exactP2Witness_claim6992 : Prop :=
  let c24 : ℕ → ℚ := fun p =>
    (∑ k ∈ Finset.range 23, (p : ℚ) ^ k) + (p : ℚ) ^ 11
  let lambdaAd : ℕ → ℚ := fun p =>
    (∑ k ∈ Finset.Icc 1 21, (p : ℚ) ^ k) +
      (MathlibPlus.Open.Research.FormalizationBatch11355.ramanujanTau p : ℚ) ^ 2 -
        (p : ℚ) ^ 11
  let rho : ℕ → ℚ := fun p => lambdaAd p / c24 p
  let displayedDecimal : ℚ := 499704435 / 1000000000
  MathlibPlus.Open.Research.FormalizationBatch11355.ramanujanTau 2 = -24 ∧
    c24 2 = 8390655 ∧
    lambdaAd 2 = 4192830 ∧
    c24 2 * rho 2 = 4192830 ∧
    rho 2 = 4192830 / 8390655 ∧
    rho 2 ≠ displayedDecimal

/-- Claim 6998: the normalized Maass-operator model gives the exact
weight-shifted second radial derivative identity and the lowering-return
coefficient. -/
def secondRadialDerivativeDecomposition_claim6998 : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℚ V]
    (R L : ℚ → V →ₗ[ℚ] V) (D : V →ₗ[ℚ] V)
    (k : ℚ) (F : V),
    R k F + L k F = (2 : ℚ) • D F →
    R (k + 2) (R k F) + L (k + 2) (R k F) =
      (2 : ℚ) • D (R k F) →
    R (k - 2) (L k F) + L (k - 2) (L k F) =
      (2 : ℚ) • D (L k F) →
    L (k + 2) (R k F) - R (k - 2) (L k F) = -k • F →
    L k F = 0 →
      (4 : ℚ) • D (D F) = R (k + 2) (R k F) - k • F ∧
      D (D F) = (1 / 4 : ℚ) • R (k + 2) (R k F) -
        (k / 4 : ℚ) • F ∧
      (k = 12 → -(k / 4 : ℚ) = -3)

/-- Claim 7001: the two displayed Maass branches recombine to the full
`-alpha/4` coefficient before the minimal PSS scalar is applied; neither
nonzero branch is annihilated separately.  The powers use the exact
integer-exponent slice, so no complex logarithm branch is introduced. -/
def recombinedDyadicCancellation_claim7001 : Prop :=
  ∀ {K : Type*} [Field K] [CharZero K]
    (s k : ℤ) (α : K),
    s ≠ 1 →
    0 < k →
    α ≠ 0 →
    α = (s : K) + (k : K) - 1 →
      let raised : K := (1 - (s : K)) / 4
      let lowering : K := -(k : K) / 4
      let pss : K := (2 : K) ^ (2 - s) / α
      raised ≠ 0 ∧
        lowering ≠ 0 ∧
        raised * pss ≠ 0 ∧
        lowering * pss ≠ 0 ∧
        raised + lowering = -α / 4 ∧
        (-α / 4) * pss = -(2 : K) ^ (-s)

end

end MathlibPlus.Open.ResearchFormalization.K0021K0031K0035
