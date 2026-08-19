import MathlibPlus.Open.ResearchFormalization.BoydWeights25796
import MathlibPlus.Open.ResearchFormalization.R0466BoydChambers

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim25792ExactPisotRootOrdering

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796
open MathlibPlus.Open.ResearchFormalization.R0466

private def integerCorrection {n : ℕ}
    (c : Fin n → ℤ) : Polynomial ℝ :=
  correctionPolynomial (fun i => (c i : ℝ))

/-- Claim 25792: in the Salem-trace Boyd setting, every integral point of a
Pisot chamber has an exterior-root witness, and its root is linearly ordered
relative to a fixed integral chamber point by evaluation of the correction
polynomial at the fixed trace value. -/
def claim25792 : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ),
    (isSalemPolynomial R n ∧ traceLift R ell n) →
      ∀ S : Set (Fin n → ℝ),
        pisotChamber n (traceToReal ell) S →
          ∀ c₀ : Fin n → ℤ,
            coefficientVector (integerCorrection c₀) ∈ S →
              ∃ (q₀ A₀ : Polynomial ℝ) (θ₀ : ℝ),
                affineBoydFormula n (traceToReal ell)
                    (integerCorrection c₀) q₀ A₀ ∧
                  exteriorRoot A₀ θ₀ ∧
                    ∀ c : Fin n → ℤ,
                      coefficientVector (integerCorrection c) ∈ S →
                        ∃ (q A : Polynomial ℝ) (θ : ℝ),
                          affineBoydFormula n (traceToReal ell)
                              (integerCorrection c) q A ∧
                            exteriorRoot A θ ∧
                              let x₀ := θ₀ + θ₀⁻¹
                              let delta :=
                                integerCorrection c - integerCorrection c₀
                              (θ₀ ≤ θ ↔
                                0 ≤ Polynomial.eval x₀ delta) ∧
                                (θ ≤ θ₀ ↔
                                  Polynomial.eval x₀ delta ≤ 0)

end

end MathlibPlus.Open.ResearchFormalization.Claim25792ExactPisotRootOrdering
