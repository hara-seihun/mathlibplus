import Mathlib

namespace MathlibPlus.Open.SectionTransporter

universe u v

variable {A : Type u} {B : Type v}

def sectionOver [AddGroup A] [AddGroup B]
    (S : Set (A × B)) (a : A) : Set B :=
  {b | (a, b) ∈ S}

def inverseClosed [AddGroup G] (S : Set G) : Prop :=
  ∀ x, x ∈ S → -x ∈ S

def productTransporter [AddGroup A] [AddGroup B]
    (S T : Set (A × B)) (α : A ≃+ A) (β : B ≃+ B) : Prop :=
  ∀ x : A × B, x ∈ S ↔ (α x.1, β x.2) ∈ T

def simultaneousSectionTransporter [AddGroup A] [AddGroup B]
    (S T : Set (A × B)) (α : A ≃+ A) (β : B ≃+ B) : Prop :=
  ∀ a : A, β '' sectionOver S a = sectionOver T (α a)

/-- Claim 57658: one product automorphism uses one common second-factor map. -/
def claim_57658 [AddGroup A] [AddGroup B]
    (S T : Set (A × B)) : Prop :=
  (0 ∉ S ∧ 0 ∉ T ∧ inverseClosed S ∧ inverseClosed T) →
    ∀ (α : A ≃+ A) (β : B ≃+ B),
      productTransporter S T α β ↔
        simultaneousSectionTransporter S T α β

end MathlibPlus.Open.SectionTransporter
