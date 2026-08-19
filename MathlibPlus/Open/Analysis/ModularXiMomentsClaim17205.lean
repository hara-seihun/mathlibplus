import MathlibPlus.NumberTheory.CompletedZetaRadial

open scoped BigOperators Topology

namespace MathlibPlus.Open.Analysis.ModularXiMomentsClaim17205

open MathlibPlus.NumberTheory.CompletedZetaRadial

noncomputable section

private noncomputable def modularXiTransform (w : ℂ) : ℂ :=
  riemannXi ((1 / 2 : ℂ) + Complex.sqrt w) / riemannXi (1 / 2 : ℂ)

private noncomputable def modularWeylCandidate (z : ℂ) : ℂ :=
  deriv modularXiTransform (-z) / modularXiTransform (-z)

/-- The canonical modular Xi logarithmic derivative has the stated local
Taylor-moment expansion. -/
def modularXiLogDerivativeMoments_claim17205 : Prop :=
  ∃ q : ℕ → ℂ, ∃ ε : ℝ, 0 < ε ∧
    ∀ z : ℂ, ‖z‖ < ε →
      Summable (fun k : ℕ => q (k + 1) * z ^ k) ∧
        modularWeylCandidate z = ∑' k : ℕ, q (k + 1) * z ^ k

end

end MathlibPlus.Open.Analysis.ModularXiMomentsClaim17205
