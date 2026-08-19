import MathlibPlus.Open.Research.Batch13518_13519
import MathlibPlus.Open.ResearchFormalization.O0091Claim13487
import MathlibPlus.Open.ResearchFormalization.O0091Claim13489
import MathlibPlus.Open.ResearchFormalization.O0091Claim13491

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13492

noncomputable section

abbrev Qubit := MathlibPlus.Open.ResearchFormalization.O0091Claim13487.Qubit
abbrev QIndex := MathlibPlus.Open.Research.QIndex
abbrev QMatrix := MathlibPlus.Open.Research.QMatrix
abbrev ChoiIndex := MathlibPlus.Open.ResearchFormalization.O0091Claim13491.ChoiIndex
abbrev ChoiMatrix := MathlibPlus.Open.ResearchFormalization.O0091Claim13491.ChoiMatrix

/-- A negative real eigenvalue on the normalized Choi partial-transpose
carrier. -/
def hasNegativeEigenvalue (M : ChoiMatrix) : Prop :=
  ∃ μ : ℝ, μ < 0 ∧
    ∃ v : ChoiIndex → ℂ, v ≠ 0 ∧
      M.mulVec v = (μ : ℂ) • v

/-- The rank-one product projectors in the joint local-X basis. -/
def jointXProjector (i : QIndex) : QMatrix :=
  MathlibPlus.Open.ResearchFormalization.O0091Claim13487.tensor
    (MathlibPlus.Open.ResearchFormalization.O0091Claim13487.projector
      (MathlibPlus.Open.ResearchFormalization.O0091Claim13487.xEigenvector i.1))
    (MathlibPlus.Open.ResearchFormalization.O0091Claim13487.projector
      (MathlibPlus.Open.ResearchFormalization.O0091Claim13487.xEigenvector i.2))

/-- The explicit joint-X measure-and-prepare channel. -/
def jointXMeasurePrepare (A : QMatrix) : QMatrix :=
  ∑ i : QIndex,
    Matrix.trace (jointXProjector i * A) • jointXProjector i

/-- Claim 13492: on the heat range the concrete heat channel is
entanglement-breaking exactly at full Reynolds, nonzero heat has a negative
Choi partial-transpose eigenvalue, the endpoint is joint-X
measure-and-prepare, and no finite positive heat time is entanglement-breaking. -/
def claim13492 : Prop :=
  (∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    (MathlibPlus.Open.Research.entanglementBreaking
        (MathlibPlus.Open.Research.heat lam) ↔ lam = 0)) ∧
    (∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 → lam ≠ 0 →
      hasNegativeEigenvalue
        (MathlibPlus.Open.ResearchFormalization.O0091Claim13491.normalizedChoiPartialTranspose
          lam)) ∧
    (∀ A : QMatrix,
      MathlibPlus.Open.Research.heat 0 A = jointXMeasurePrepare A) ∧
    (∀ τ : ℝ, 0 < τ →
      ¬ MathlibPlus.Open.Research.entanglementBreaking
        (MathlibPlus.Open.Research.heat (Real.exp (-2 * τ))))

end

end MathlibPlus.Open.ResearchFormalization.O0091Claim13492
