import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

section AffineFibers

variable {A B : Type*}

/-- The pointwise exponent-two condition for an elementary abelian 2-group. -/
def elementaryAbelianTwo (A : Type*) [AddCommGroup A] : Prop :=
  ∀ a : A, a + a = 0

/-- The normalized identity-base affine fiber map from the packet. -/
def identityBaseAffineMap [AddCommGroup A] [AddCommGroup B]
    (L : A → B ≃+ B) (c : A → B) : A × B → A × B :=
  fun p => (p.1, L p.1 p.2 + c p.1)

/-- Claim 27707: the normalized identity-base affine fiber profile. -/
def claim27707 [Fintype A] [AddCommGroup A]
    [Fintype B] [AddCommGroup B]
    (hA : elementaryAbelianTwo A)
    (f : A × B → A × B)
    (L : A → B ≃+ B) (c : A → B) : Prop :=
  (∀ b : B, L 0 b = b) ∧ c 0 = 0 ∧
    (∀ a : A, ∀ b : B,
      f (a, b) = (a, L a b + c a))

end AffineFibers

section CommonAffineFiber

variable {A B : Type*}

/-- The common affine map on the active fibers in Claim 27747. -/
noncomputable def commonAffineFiberMap [AddCommGroup A] [AddCommGroup B]
    (U : Set B) (L : A ≃+ A) (t : A) : B × A → B × A := by
  classical
  exact fun p =>
    if p.1 ∈ U then (p.1, L p.2 + t) else (p.1, p.2)

/-- Claim 27747: one affine permutation is used on every active base fiber. -/
def claim27747 [Fintype A] [AddCommGroup A]
    [Fintype B] [AddCommGroup B]
    (hB : elementaryAbelianTwo B)
    (hAodd : Odd (Fintype.card A))
    (U : Set B) (hU : ∀ b : B, b ∈ U → b ≠ 0)
    (f : B × A → B × A)
    (L : A ≃+ A) (t : A) : Prop :=
  (∀ b : B, b ∈ U → b ≠ 0) ∧
    (∀ b : B, ∀ x : A,
      f (b, x) = by
        classical
        exact if b ∈ U then (b, L x + t) else (b, x))

end CommonAffineFiber

end MathlibPlus.Open.ResearchFormalization
