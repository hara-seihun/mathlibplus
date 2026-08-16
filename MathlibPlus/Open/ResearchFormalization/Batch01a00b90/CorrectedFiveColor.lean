import MathlibPlus.Open.GraphTheory.R0943

namespace MathlibPlus.Open.ResearchFormalization.CorrectedFiveColor

open MathlibPlus.Open.GraphTheory.R0943

abbrev QuaternionCarrier := QuaternionGroup 2
abbrev QuotientVector := V4
abbrev QuotientFiber := V4Group

/-- An ordinary inverse-closed connection set, with the inverse relation
written in both directions. -/
def ordinaryInverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ g : G, g ∈ S ↔ g⁻¹ ∈ S

/-- The loopless condition for an ordinary Cayley connection set. -/
def ordinaryIdentityFree {G : Type*} [Group G] (S : Set G) : Prop :=
  (1 : G) ∉ S

/-- The actual Cayley-presentation relation carried by a permutation. -/
def ordinaryCayleyPresentation
    {G : Type*} [Group G]
    (S T : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y : G, x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T

/-- The quotient action on the odd factor of the full-V4 branch. -/
def hasQuotientAction {A : Type*} [Group A]
    (f : Equiv.Perm (A × QuaternionCarrier)) (α : A ≃* A) : Prop :=
  ∀ a : A, ∀ q : QuaternionCarrier, (f (a, q)).1 = α a

/-- The group automorphism lifted from the quotient action, leaving the
quaternion coordinate unchanged. -/
def liftedGroupAutomorphism {A : Type*} [Group A]
    (α : A ≃* A) : A × QuaternionCarrier → A × QuaternionCarrier :=
  fun x => (α x.1, x.2)

/-- The inverse quotient action used to express the normalized residual. -/
def liftedGroupAutomorphismInverse {A : Type*} [Group A]
    (α : A ≃* A) : A × QuaternionCarrier → A × QuaternionCarrier :=
  fun x => (α.symm x.1, x.2)

/-- A normalized actual quotient-image presentation map.  The first
coordinate is the prescribed quotient action, while the map itself carries
one source connection set to the target. -/
def actualQuotientImagePresentation
    {A : Type*} [Group A]
    (S T : Set (A × QuaternionCarrier))
    (f : Equiv.Perm (A × QuaternionCarrier)) (α : A ≃* A) : Prop :=
  f (1 : A × QuaternionCarrier) = 1 ∧
    hasQuotientAction f α ∧
    ordinaryCayleyPresentation S T f ∧
    Set.image f S = T

/-- The identity-base affine residual on the characteristic four-point
quotient.  The equation is stated through the verified quaternion-to-V4
quotient, so no abstract fibre carrier is substituted for the source one. -/
def normalizedQuotientResidual
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

/-- Claim 39030: in the full-V4 branch the residual conclusion is only
conditional on an actual quotient-image presentation map; the explicit
C5/V4 boundary records why a color shadow alone is not that premise. -/
def claim39030 : Prop :=
  (∀ {A : Type*} [Fintype A] [CommGroup A],
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
              Set.image (liftedGroupAutomorphism α) S = T) ∧
  (let A := ZMod 5
   let d₁ : ZMod 2 × ZMod 2 := (1, 0)
   let d₂ : ZMod 2 × ZMod 2 := (0, 1)
   let boundarySection : A → Finset (ZMod 2 × ZMod 2) := fun a =>
     if a = 1 ∨ a = -1 then {d₁}
     else if a = 2 ∨ a = -2 then {d₂}
     else ∅
   let color : A → Fin 5 := fun a => if a = 0 then 0 else 1
   let shadow : A → A := fun a => 2 * a
   let liftedSection : A → Finset (ZMod 2 × ZMod 2) := fun a =>
     boundarySection (3 * a)
   d₁ ≠ d₂ ∧
     color 0 = 0 ∧
     (∀ a : A, color (-a) = color a) ∧
     boundarySection 0 = ∅ ∧
     (∀ a : A, boundarySection (-a) = boundarySection a) ∧
     (∀ a : A, a ≠ 0 → color a = 1) ∧
     Function.Bijective shadow ∧
     (∀ a : A, color (shadow a) = color a) ∧
     liftedSection 2 = {d₁} ∧
     boundarySection 2 = {d₂} ∧
     liftedSection 2 ≠ boundarySection 2)

end MathlibPlus.Open.ResearchFormalization.CorrectedFiveColor
