import MathlibPlus.Open.ResearchFormalization.R0106AnchoredExterior

namespace MathlibPlus.Open.ResearchFormalization.R0106AnchoredExteriorRepair

open scoped InnerProductSpace
open MathlibPlus.Open.ResearchFormalization.R0106AnchoredExterior

noncomputable section

/-- The orthogonal-sum pairing on the displayed carrier `ℝ ⊕ Λ²V`. -/
noncomputable def orthogonalSumPairing
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : ℝ × (⋀[ℝ]^2 V)) : ℝ :=
  x.1 * y.1 + exteriorTwoPairing x.2 y.2

/-- The anchored exterior dilation on an arbitrary real inner-product space. -/
noncomputable def anchoredExteriorDilation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e v : V) : ℝ × (⋀[ℝ]^2 V) :=
  (⟪e, v⟫_ℝ, exteriorWedge2 e v)

/-- Claim 17994: the anchored exterior dilation preserves the inner product. -/
def claim17994 : Prop :=
  ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e v w : V),
    ‖e‖ = 1 →
      orthogonalSumPairing (anchoredExteriorDilation e v)
          (anchoredExteriorDilation e w) = ⟪v, w⟫_ℝ

end

end MathlibPlus.Open.ResearchFormalization.R0106AnchoredExteriorRepair
