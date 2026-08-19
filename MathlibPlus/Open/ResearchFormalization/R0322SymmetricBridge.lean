import MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0322DoubleSpiderClaims

namespace MathlibPlus.Open.ResearchFormalization.R0322SymmetricBridge

noncomputable section

abbrev ScalarPoly := R0322DoubleSpiderClaims.ScalarPoly
abbrev LegFamily := R0322DoubleSpiderClaims.LegFamily

/-- The rooted-tree bridge gluing carrier, with the diagonal form
`J = diag(t,-1,-XQ)` fixed by the reviewed transfer construction. -/
def rootedBridgeGluing (A B : LegFamily) : ScalarPoly :=
  R0322DoubleSpiderClaims.bilinearResponse
    (R0322DoubleSpiderClaims.sideResponse A)
    (R0322DoubleSpiderClaims.sideResponse B)
    R0322DoubleSpiderClaims.bridgeMatrix

/-- Claim 19828: the explicit rooted bridge pairing is `x_Rᵀ J x_S`, and
all bridge kernels `J M^(c-1)` are symmetric because the reviewed transfer
matrix is self-adjoint for the reviewed diagonal gluing form. -/
def symmetricBridgeGluing_claim19828 : Prop :=
  (∀ A B : LegFamily,
    rootedBridgeGluing A B =
      ∑ i : Fin 3, ∑ j : Fin 3,
        R0322DoubleSpiderClaims.sideResponse A i *
          R0322DoubleSpiderClaims.bridgeMatrix i j *
          R0322DoubleSpiderClaims.sideResponse B j) ∧
    R0322DoubleSpiderClaims.transferMatrix.transpose *
        R0322DoubleSpiderClaims.bridgeMatrix =
      R0322DoubleSpiderClaims.bridgeMatrix *
        R0322DoubleSpiderClaims.transferMatrix ∧
    (∀ c : ℕ,
      (R0322DoubleSpiderClaims.bridgeMatrix *
          R0322DoubleSpiderClaims.transferMatrix ^ (c - 1)).transpose =
        R0322DoubleSpiderClaims.bridgeMatrix *
          R0322DoubleSpiderClaims.transferMatrix ^ (c - 1))

end

end MathlibPlus.Open.ResearchFormalization.R0322SymmetricBridge
