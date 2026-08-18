import MathlibPlus.Open.ResearchFormalization.R1153

namespace MathlibPlus.Open.ResearchFormalization.R1153Claim31630

noncomputable section

abbrev Q8 := QuaternionGroup 2
abbrev Q8Center := Subgroup.center Q8
abbrev Q8Quotient := Q8 ⧸ Q8Center
abbrev C2 := Multiplicative (ZMod 2)
abbrev C2Squared := C2 × C2
abbrev ProductQuotient (A : Type*) := A × Q8Quotient
abbrev ProductGroup (A : Type*) := A × Q8

/-- The quotient projection on the odd Hall factor and the quaternion
quotient factor. -/
def quotientProjection31630
    {A : Type*} [CommGroup A] : ProductGroup A →* ProductQuotient A :=
  MonoidHom.prod (MonoidHom.fst A Q8)
    ((QuotientGroup.mk' Q8Center).comp (MonoidHom.snd A Q8))

def quotientAutRelation31630
    {A : Type*} [CommGroup A]
    (φ : MulAut (ProductGroup A))
    (ψ : MulAut (ProductQuotient A)) : Prop :=
  ∀ g : ProductGroup A,
    quotientProjection31630 (φ g) = ψ (quotientProjection31630 g)

/-- The literal quaternionic central involution in the product model. -/
def quaternionCentralInvolution31630 : Q8 := QuaternionGroup.a 2

def productCentralInvolution31630 {A : Type*} [CommGroup A] : ProductGroup A :=
  (1, quaternionCentralInvolution31630)

def quotientLiftFixingCentral31630
    {A : Type*} [CommGroup A]
    (φ : MulAut (ProductGroup A))
    (ψ : MulAut (ProductQuotient A)) : Prop :=
  quotientAutRelation31630 φ ψ ∧
    φ (productCentralInvolution31630 (A := A)) =
      productCentralInvolution31630 (A := A)

/-- Claim 31630: after identifying the quaternion quotient with the Klein
four group, the quotient automorphism map is surjective, and every aligned
quotient automorphism has a lift fixing the literal central involution. -/
def claim31630 : Prop :=
  ∀ (A : Type*) [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    Nonempty (Q8Quotient ≃* C2Squared) ∧
      ∀ ψ : MulAut (ProductQuotient A),
        ∃ φ : MulAut (ProductGroup A),
          quotientLiftFixingCentral31630 φ ψ

end
end MathlibPlus.Open.ResearchFormalization.R1153Claim31630
