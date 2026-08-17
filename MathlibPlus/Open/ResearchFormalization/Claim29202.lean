import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim29202

/-- Automorphisms of a graph or digraph presented by its adjacency relation. -/
def automorphismSet {X : Type*} (Γ : X → X → Prop) : Set (Equiv.Perm X) :=
  {a | ∀ x y, Γ (a x) (a y) ↔ Γ x y}

/-- A permutation subgroup is regular when it contains exactly one transporter
between every ordered pair of points. -/
def regularSubgroup {X : Type*} (R : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ x y : X, ∃! r : Equiv.Perm X, r ∈ R ∧ r x = y

/-- The actual permutations induced on a quotient map by a set of
permutations. -/
def quotientImage {X Q : Type*} (q : X → Q) (S : Set (Equiv.Perm X)) :
    Set (Equiv.Perm Q) :=
  {aq | ∃ a, a ∈ S ∧ ∀ x, aq (q x) = q (a x)}

/-- Conjugacy by a permutation in a specified ambient set. -/
def conjugateWithin {X : Type*} (A : Set (Equiv.Perm X))
    (R T : Subgroup (Equiv.Perm X)) : Prop :=
  ∃ a, a ∈ A ∧ ∀ r : Equiv.Perm X, r ∈ R ↔ a * r * a⁻¹ ∈ T

/-- The binary elementary-abelian group used for the base of the Cayley
product. -/
abbrev binaryCayleyGroup (d : ℕ) (B : Type*) [AddCommGroup B] :=
  Multiplicative ((Fin d → ZMod 2) × B)

/-- Conjugacy of the actual induced quotient images, not of a larger
abstract quotient automorphism group. -/
def quotientConjugate {X Q : Type*} (q : X → Q)
    (A : Set (Equiv.Perm X)) (R T : Subgroup (Equiv.Perm X)) : Prop :=
  ∃ aq : Equiv.Perm Q,
    aq ∈ quotientImage q A ∧
      ∀ r : Equiv.Perm Q,
        r ∈ quotientImage q R ↔ aq * r * aq⁻¹ ∈ quotientImage q T

/-- Claim 29202: conjugacy of regular copies in the actual automorphism group
is equivalent to conjugacy of their actual induced copies on the common
two-point quotient. -/
def claim29202 : Prop :=
  ∀ (d : ℕ) (B : Type*) [AddCommGroup B] [Fintype B]
    (Γ : binaryCayleyGroup d B → binaryCayleyGroup d B → Prop)
    (Q : Type*) [Fintype Q]
    (q : binaryCayleyGroup d B → Q)
    (R T : Subgroup (Equiv.Perm (binaryCayleyGroup d B))),
    0 < d →
    Odd (Fintype.card B) →
    (∀ g x y, Γ (g * x) (g * y) ↔ Γ x y) →
    Function.Surjective q →
    (∀ b : Q,
      Set.ncard {x : binaryCayleyGroup d B | q x = b} = 2) →
    (∀ a, a ∈ automorphismSet Γ →
      ∃ aq : Equiv.Perm Q, ∀ x, aq (q x) = q (a x)) →
    (∀ r : Equiv.Perm (binaryCayleyGroup d B),
      r ∈ R → r ∈ automorphismSet Γ) →
    (∀ t : Equiv.Perm (binaryCayleyGroup d B),
      t ∈ T → t ∈ automorphismSet Γ) →
    regularSubgroup R →
    regularSubgroup T →
    Nonempty (R ≃* binaryCayleyGroup d B) →
    Nonempty (T ≃* binaryCayleyGroup d B) →
    (conjugateWithin (automorphismSet Γ) R T ↔
      quotientConjugate q (automorphismSet Γ) R T)

end MathlibPlus.Open.ResearchFormalization.Claim29202
