import MathlibPlus.Open.GraphTheory.R0943

namespace MathlibPlus.Open.ResearchFormalization.ResearchFormalize39030

open MathlibPlus.Open.GraphTheory.R0943

private abbrev QuaternionCarrier := QuaternionGroup 2
private abbrev QuotientVector := V4
private abbrev QuotientFiber := V4Group

private def ordinaryInverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ g : G, g ∈ S ↔ g⁻¹ ∈ S

private def ordinaryIdentityFree {G : Type*} [Group G] (S : Set G) : Prop :=
  (1 : G) ∉ S

private def ordinaryCayleyPresentation
    {G : Type*} [Group G]
    (S T : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y : G, x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T

private def hasQuotientAction {A : Type*} [Group A]
    (f : Equiv.Perm (A × QuaternionCarrier)) (α : A ≃* A) : Prop :=
  ∀ a : A, ∀ q : QuaternionCarrier, (f (a, q)).1 = α a

private def liftedGroupAutomorphism {A : Type*} [Group A]
    (α : A ≃* A) : A × QuaternionCarrier → A × QuaternionCarrier :=
  fun x => (α x.1, x.2)

private def liftedGroupAutomorphismInverse {A : Type*} [Group A]
    (α : A ≃* A) : A × QuaternionCarrier → A × QuaternionCarrier :=
  fun x => (α.symm x.1, x.2)

private def actualQuotientImagePresentation
    {A : Type*} [Group A]
    (S T : Set (A × QuaternionCarrier))
    (f : Equiv.Perm (A × QuaternionCarrier)) (α : A ≃* A) : Prop :=
  f (1 : A × QuaternionCarrier) = 1 ∧
    hasQuotientAction f α ∧
    ordinaryCayleyPresentation S T f ∧
    Set.image f S = T

private def normalizedQuotientResidual
    {A : Type*} [Group A]
    (π : QuaternionCarrier →* QuotientFiber)
    (f : Equiv.Perm (A × QuaternionCarrier)) (α : A ≃* A)
    (r : Equiv.Perm (A × QuaternionCarrier)) : Prop :=
  (∀ x : A × QuaternionCarrier,
    r x = liftedGroupAutomorphismInverse α (f x)) ∧
    ∃ linear : A → (QuotientVector ≃+ QuotientVector),
      ∃ shift : A → QuotientVector,
        linear 1 = AddEquiv.refl QuotientVector ∧
          shift 1 = 0 ∧
          ∀ (a : A) (q : QuaternionCarrier),
            (r (a, q)).1 = a ∧
              π (r (a, q)).2 =
                Multiplicative.ofAdd
                  (linear a (Multiplicative.toAdd (π q)) + shift a)

/-- Claim 39030: the positive five-color residual statement is conditional on
an actual quotient-image presentation with the prescribed quotient action;
no converse from a five-color shadow is asserted. -/
def claim39030_conditional_actual_quotient_image : Prop :=
  ∀ {A : Type*} [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (π : QuaternionCarrier →* QuotientFiber),
      quaternionProjectionData π →
      ∀ (S T : Set (A × QuaternionCarrier))
        (f : Equiv.Perm (A × QuaternionCarrier)) (α : A ≃* A),
        ordinaryInverseClosed S →
        ordinaryIdentityFree S →
        ordinaryInverseClosed T →
        ordinaryIdentityFree T →
        actualQuotientImagePresentation S T f α →
        ∃ r : Equiv.Perm (A × QuaternionCarrier),
          normalizedQuotientResidual π f α r ∧
            derivativeInvariantSet r S ∧
            Set.image r S = S ∧
            Set.image (liftedGroupAutomorphism α) S = T

end MathlibPlus.Open.ResearchFormalization.ResearchFormalize39030
