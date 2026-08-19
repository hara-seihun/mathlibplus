import Mathlib

namespace MathlibPlus.Open.Research.ZeroLiftTransfer61178

/-- The additive Cayley relation determined by a connection set. -/
def cayleyRelation {A : Type*} [AddGroup A]
    (S : Set A) (x y : A) : Prop :=
  y - x ∈ S

/-- The connection set obtained by adjoining a zero coordinate. -/
def zeroLiftSet {A B : Type*} [Zero B]
    (S : Set A) : Set (A × B) :=
  (fun a : A => (a, 0)) '' S

/-- The coordinatewise zero-lift of a vertex map. -/
def zeroLiftMap {A B : Type*}
    (f : A → A) : A × B → A × B :=
  fun p => (f p.1, p.2)

/-- A bijection preserving and reflecting the displayed Cayley relations. -/
def cayleyRelationIsomorphism
    {A B : Type*} [AddGroup A] [AddGroup B]
    (S : Set A) (T : Set B) (F : A → B) : Prop :=
  Function.Bijective F ∧
    ∀ x y, cayleyRelation S x y ↔ cayleyRelation T (F x) (F y)

/-- Identity-freeness for an additive connection set. -/
def identityFree {A : Type*} [Zero A] (S : Set A) : Prop :=
  (0 : A) ∉ S

/-- Inverse-closure for an additive connection set. -/
def inverseClosed {A : Type*} [Neg A] (S : Set A) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

/-- The admitted field-generic zero-lift transfer theorem. -/
def zeroLiftTransferClaim61178
    {R H : Type*} [Field R] [AddCommGroup H] [Module R H] : Prop :=
  ∀ (S T : Set H) (f : H → H),
    Submodule.span R S = ⊤ →
    Submodule.span R T = ⊤ →
    Function.Bijective f →
    (∀ x y, cayleyRelation S x y ↔ cayleyRelation T (f x) (f y)) →
    (¬ ∃ e : H ≃ₗ[R] H, e '' S = T) →
    ∀ (K : Type*) [AddCommGroup K] [Module R K],
      cayleyRelationIsomorphism
          (zeroLiftSet (B := K) S)
          (zeroLiftSet (B := K) T)
          (zeroLiftMap (B := K) f) ∧
      (¬ ∃ e : (H × K) ≃ₗ[R] (H × K),
        e '' zeroLiftSet (B := K) S = zeroLiftSet (B := K) T) ∧
      (identityFree S →
        identityFree (zeroLiftSet (B := K) S)) ∧
      (inverseClosed S →
        inverseClosed (zeroLiftSet (B := K) S)) ∧
      (identityFree T →
        identityFree (zeroLiftSet (B := K) T)) ∧
      (inverseClosed T →
        inverseClosed (zeroLiftSet (B := K) T))

end MathlibPlus.Open.Research.ZeroLiftTransfer61178
