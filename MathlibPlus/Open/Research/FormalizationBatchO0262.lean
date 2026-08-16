import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchO0262

noncomputable section

open scoped BigOperators Matrix
open Filter
open MeasureTheory

/-- The explicit hypotheses carried by a certified simple critical zero. -/
def certifiedSimpleCriticalZero (ρ : ℂ) : Prop :=
  ρ.re = (1 / 2 : ℝ) ∧
    riemannZeta ρ = 0 ∧
      deriv riemannZeta ρ ≠ 0 ∧ ρ ≠ 0

/-- The packet formula away from its removable point. -/
noncomputable def rawCriticalZeroPacket (ρ : ℂ) (y : ℝ) : ℂ :=
  riemannZeta (ρ + Complex.I * (y : ℂ)) *
      Complex.Gamma (-Complex.I * (y : ℂ)) /
    ((ρ + Complex.I * (y : ℂ)) * deriv riemannZeta ρ)

/-- The normalized critical-zero packet with its stated value at zero. -/
noncomputable def criticalZeroPacket (ρ : ℂ) (y : ℝ) : ℂ :=
  if y = 0 then -(1 : ℂ) / ρ else rawCriticalZeroPacket ρ y

/-- The scalar Gram limit from the packet energy. -/
noncomputable def atomicGramConstant (ρ : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖criticalZeroPacket ρ y‖ ^ 2

/-- The fixed-atom packet Gram entry at scale `N`. -/
noncomputable def atomicPacketGramEntry
    (ρ : ℂ) (N : ℝ) {J : ℕ} (x : Fin J → ℝ)
    (j k : Fin J) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ y : ℝ,
      ((‖criticalZeroPacket ρ y‖ ^ 2 : ℝ) : ℂ) *
        Complex.exp
          (-Complex.I * (((x j - x k : ℝ) : ℂ)) * (y : ℂ) *
            (Real.log N : ℂ))

/-- The matrix of fixed-atom packet Gram entries. -/
noncomputable def atomicPacketGram
    (ρ : ℂ) (N : ℝ) (J : ℕ) (x : Fin J → ℝ) :
    Matrix (Fin J) (Fin J) ℂ :=
  fun j k => atomicPacketGramEntry ρ N x j k

/-- The scalar matrix with the packet Gram limit on its diagonal. -/
noncomputable def scalarIdentityMatrix (J : ℕ) (C : ℝ) :
    Matrix (Fin J) (Fin J) ℂ :=
  fun j k => if j = k then (C : ℂ) else 0

/-- The operator norm of a finite complex matrix acting by left multiplication. -/
noncomputable def matrixOperatorNorm {J : ℕ}
    (A : Matrix (Fin J) (Fin J) ℂ) : ℝ :=
  ((Matrix.mulVecLin A).toContinuousLinearMap).opNorm

/-- Claim 15072: fixed atomic packet Gram convergence. -/
def claim_15072 : Prop :=
  ∀ (ρ : ℂ) (J : ℕ) (x : Fin J → ℝ),
    certifiedSimpleCriticalZero ρ →
    0 < J →
    Function.Injective x →
      let Cρ := atomicGramConstant ρ
      Cρ > 0 ∧
        (∀ j k : Fin J,
          Tendsto
            (fun N : ℝ => atomicPacketGramEntry ρ N x j k)
            atTop
            (nhds (if j = k then (Cρ : ℂ) else 0))) ∧
        Tendsto
          (fun N : ℝ =>
            matrixOperatorNorm
              (atomicPacketGram ρ N J x - scalarIdentityMatrix J Cρ))
          atTop
          (nhds 0)

end

end MathlibPlus.Open.Research.FormalizationBatchO0262
