import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0106AnchoredExterior

open scoped InnerProductSpace

noncomputable section

/-- The canonical induced pairing on the second exterior power, defined from
`innerₗ` and the exterior-power dual pairing without a finite-dimensional
assumption. -/
noncomputable def exteriorTwoPairing
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : ⋀[ℝ]^2 V) : ℝ :=
  exteriorPower.pairingDual ℝ V 2
    ((exteriorPower.map 2 (innerₗ V)) x) y

/-- The decomposable second exterior product of two vectors. -/
noncomputable def exteriorWedge2
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) : ⋀[ℝ]^2 V :=
  exteriorPower.ιMulti ℝ 2 ![u, v]

/-- Claim 17993: for a unit anchor in an arbitrary real inner-product space,
the induced second-exterior-power pairing has the anchored Gram identity. -/
def anchoredExteriorInnerProduct_claim17993 : Prop :=
  ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e v w : V),
    ‖e‖ = 1 →
      exteriorTwoPairing (exteriorWedge2 e v) (exteriorWedge2 e w) =
        ⟪v, w⟫_ℝ - ⟪e, v⟫_ℝ * ⟪e, w⟫_ℝ

end

end MathlibPlus.Open.ResearchFormalization.R0106AnchoredExterior
