import MathlibPlus.Open.NumberTheory.AdmittedPrimeEdgeBatch
import MathlibPlus.NumberTheory.CompletedZetaRadial

namespace MathlibPlus.Open.NumberTheory.FormalizationBatchClaim15456

open Filter
open scoped Topology
open MathlibPlus.Open.NumberTheory.FormalizationBatch

noncomputable section

/-- The quartic factor multiplying the completed Xi carrier. -/
noncomputable def quarticMultiplier (R : ℝ) (s : ℂ) : ℂ :=
  1 + (s - (1 / 2 : ℂ)) ^ 4 / (R : ℂ) ^ 4

/-- The completed carrier named `Xi` in the quartic modification. -/
noncomputable def completedXi (s : ℂ) : ℂ :=
  MathlibPlus.NumberTheory.CompletedZetaRadial.riemannXi s

/-- The modified completed Xi carrier `tilde Xi_R`. -/
noncomputable def modifiedCompletedXi (R : ℝ) (s : ℂ) : ℂ :=
  quarticMultiplier R s * completedXi s

/-- The de-archimedeanized carrier paired with the canonical Xi prime-log
normalization.  Removing the completed archimedean factor leaves `zeta`. -/
noncomputable def deArchimedeanizedXi (s : ℂ) : ℂ :=
  riemannZeta s

/-- The de-archimedeanized carrier of the modified completed Xi. -/
noncomputable def modifiedDeArchimedeanizedXi (R : ℝ) (s : ℂ) : ℂ :=
  quarticMultiplier R s * deArchimedeanizedXi s

/-- The prime-log derivative of the modified carrier, defined from that
carrier rather than from the claimed correction formula. -/
noncomputable def modifiedPrimeLogDerivative (R : ℝ) (s : ℂ) : ℂ :=
  -deriv (modifiedDeArchimedeanizedXi R) s /
    modifiedDeArchimedeanizedXi R s

/-- Claim 15456: the quartic multiplier violates the prime-edge law. -/
def claim15456 : Prop :=
  ∀ R : ℝ, 0 < R →
    (∀ s : ℂ, modifiedDeArchimedeanizedXi R s ≠ 0 →
      modifiedPrimeLogDerivative R s =
        deArchimedeanPrimeLogDerivative s -
          4 * (s - (1 / 2 : ℂ)) ^ 3 /
            ((R : ℂ) ^ 4 + (s - (1 / 2 : ℂ)) ^ 4)) ∧
      Tendsto
        (fun x : ℝ => (x : ℂ) * modifiedPrimeLogDerivative R (x : ℂ))
        atTop (𝓝 (-4 : ℂ))

end

end MathlibPlus.Open.NumberTheory.FormalizationBatchClaim15456
