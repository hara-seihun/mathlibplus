import MathlibPlus.Open.LinearAlgebra.BatchO0091

namespace MathlibPlus.Open.LinearAlgebra.BatchO0091Claim13493

open MathlibPlus.Open.LinearAlgebra

/-- The encoded `(++ , --)` relative-qubit sector intertwines the full heat
channel with the qubit dephasing channel for every matrix input. -/
def exactEncodedDephasingSubchannel_claim13493 : Prop :=
  ∀ (lam : ℝ) (rho : QMatrix),
    heatChannel lam (encodeRelativeQubit rho) =
      encodeRelativeQubit (qubitDephasing lam rho)

end MathlibPlus.Open.LinearAlgebra.BatchO0091Claim13493
