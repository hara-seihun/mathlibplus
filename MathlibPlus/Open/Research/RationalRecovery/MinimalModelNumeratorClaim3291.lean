import Mathlib
import MathlibPlus.Open.NewResearch2.RationalHankel15108
import MathlibPlus.Open.ResearchFormalization.MatchingPencilError15118

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.Research.RationalRecovery

noncomputable section

open MathlibPlus.Open.NewResearch2.RationalHankel15108
open MathlibPlus.Open.NewResearch2.RationalHankelStructure
open MathlibPlus.Open.ResearchFormalization.MatchingPencilError15118

private def coefficientL1Norm (Q : Polynomial ℂ) : ℝ :=
  ∑ k ∈ Q.support, ‖Q.coeff k‖

private def reconstructedNumerator
    {d : ℕ} (q : ℕ → ℂ) (c : ℕ → Fin d → ℂ) (n : ℕ) : Fin d → ℂ :=
  fun i => ∑ k ∈ Finset.range (n + 1), q k * c (n - k) i

/-- Claim 3291: the vector minimal-model numerator reconstruction has the
stated finite two-norm error, with the observed denominator coefficient
radius and the observed vector coefficient sequence kept explicit. -/
def minimal_model_numerator_reconstruction_error_claim3291 : Prop :=
  ∀ (d : ℕ) (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ),
    properVectorRationalModel P Q →
      let Qstar := reducedDenominator P Q
      let Pstar := reducedNumerator P Q
      let r := Qstar.natDegree
      ∀ (Qhat : Polynomial ℂ)
        (ctilde : ℕ → Fin d → ℂ)
        (epsilon : ℕ → ℝ) (deltaQ : ℝ),
        Qhat.coeff 0 = 1 →
        Qhat.natDegree ≤ r →
        0 ≤ deltaQ →
        coefficientL1Norm (Qhat - Qstar) ≤ deltaQ →
        (∀ n : ℕ,
          0 ≤ epsilon n ∧
            vectorTwoNorm (fun i =>
              ctilde n i - vectorTaylorCoeff Pstar Qstar n i) ≤ epsilon n) →
        let qhat : ℕ → ℂ := fun k => Qhat.coeff k
        let pHat : ℕ → Fin d → ℂ :=
          reconstructedNumerator qhat ctilde
        let p : ℕ → Fin d → ℂ := fun n i => (Pstar i).coeff n
        let Elt : ℝ := ∑ n ∈ Finset.range r, epsilon n
        let Ctilde : ℝ :=
          ∑ n ∈ Finset.range r, vectorTwoNorm (ctilde n)
        let deltaP : ℝ :=
          (coefficientL1Norm Qhat + deltaQ) * Elt + deltaQ * Ctilde
        (∑ n ∈ Finset.range r,
          vectorTwoNorm (fun i => pHat n i - p n i)) ≤ deltaP

end
end MathlibPlus.Open.Research.RationalRecovery
