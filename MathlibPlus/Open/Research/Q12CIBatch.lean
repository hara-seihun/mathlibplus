import Mathlib

namespace MathlibPlus.Open.Research.Q12

def isQ12Presentation {G : Type*} [Group G] [Fintype G] (a b : G) : Prop :=
  Fintype.card G = 12 ∧
  orderOf a = 6 ∧
  b ^ 2 = a ^ 3 ∧
  b⁻¹ * a * b = a⁻¹ ∧
  (∀ g : G, ∃ i : Fin 6,
    g = a ^ (i : ℕ) ∨ g = a ^ (i : ℕ) * b)

def cayleyRel {G : Type*} [Group G] (S : Set G) (x y : G) : Prop :=
  x⁻¹ * y ∈ S

def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ g, g ∈ S ↔ g⁻¹ ∈ S

def relationLabeledIso {G I : Type*} [Group G] (S T : I → Set G)
    (e : Equiv G G) : Prop :=
  ∀ i x y, cayleyRel (S i) x y ↔ cayleyRel (T i) (e x) (e y)

/-- The symmetric, relation-labeled CI assertion for the twelve-element
quaternion/dicyclic presentation. -/
def symmetricBinaryQ12CI : Prop :=
  ∀ {G : Type*} [Group G] [Fintype G]
    {I : Type*} [Fintype I]
    (a b : G),
    isQ12Presentation a b →
    ∀ (S T : I → Set G),
      (∀ i, inverseClosed (S i) ∧ inverseClosed (T i)) →
      ∀ e : Equiv G G,
        relationLabeledIso S T e →
        ∃ phi : G ≃* G, ∀ i x y,
          cayleyRel (S i) x y ↔ cayleyRel (T i) (phi x) (phi y)

end MathlibPlus.Open.Research.Q12
