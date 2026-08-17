import MathlibPlus.Open.ResearchFormalizationBatch_01a003cb_d995_7564_b82d_d782ff7e0528

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- Under C(0)=0, constancy in x of every projected derivative is exactly the
recorded value theta(C(h)). -/
def claim_38302 : Prop :=
  ∀ {H : Type*} [AddCommGroup H] [Module TernaryScalar H]
    (L : (TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar) →
      Submodule TernaryScalar H)
    (C : H → TernaryDualCarrier),
    C 0 = 0 →
      ((∀ theta : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar,
          theta ∈ fourCharacterSet → ∀ h : H, h ∈ L theta →
          ∃ c : TernaryScalar, ∀ x : H,
            theta (C (x + h)) - theta (C x) = c) ↔
        (∀ theta : TernaryDualCarrier →ₗ[TernaryScalar] TernaryScalar,
          theta ∈ fourCharacterSet → ∀ h : H, h ∈ L theta →
          ∀ x : H,
            theta (C (x + h)) - theta (C x) = theta (C h)))

end MathlibPlus.Open.ResearchFormalizationBatch
