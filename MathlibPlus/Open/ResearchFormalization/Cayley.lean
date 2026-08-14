import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The regular elementary abelian group used for `C_p^n`. -/
abbrev cyclicPower (p n : ℕ) := Multiplicative (Fin n → ZMod p)

/-- An undirected simple adjacency relation. -/
def IsUndirectedSimple {α : Type*} (adj : α → α → Prop) : Prop :=
  (∀ x, ¬ adj x x) ∧ ∀ x y, adj x y ↔ adj y x

/-- Preservation of adjacency by a permutation. -/
def IsGraphAutomorphism {α : Type*} (adj : α → α → Prop)
    (φ : Equiv.Perm α) : Prop :=
  ∀ x y, adj x y ↔ adj (φ x) (φ y)

/-- Left translation in the regular action of a group on itself. -/
def leftTranslation {R : Type*} [Group R] (r : R) : Equiv.Perm R :=
  { toFun := fun x => r * x
    invFun := fun x => r⁻¹ * x
    left_inv := by
      intro x
      simp [mul_assoc]
    right_inv := by
      intro x
      simp [mul_assoc] }

/-- Inversion as a permutation of a group. -/
def inversionPermutation {R : Type*} [Group R] : Equiv.Perm R :=
  { toFun := fun x => x⁻¹
    invFun := fun x => x⁻¹
    left_inv := by
      intro x
      simp
    right_inv := by
      intro x
      simp }

/-- The Cayley adjacency relation attached to a connection set. -/
def cayleyAdj {R : Type*} [Group R] (S : Set R) (x y : R) : Prop :=
  x⁻¹ * y ∈ S

/--
Claim 58168: inversion is an actual graph automorphism and extends the regular
translation subgroup by the indicated inversion conjugation.
-/
def claim58168
    {R : Type*} [CommGroup R]
    (p n : ℕ) (hp : Nat.Prime p)
    (_iso : R ≃* cyclicPower p n)
    (S : Set R) (adj : R → R → Prop) : Prop :=
  (IsUndirectedSimple adj ∧
      (∀ x y, adj x y ↔ cayleyAdj S x y) ∧
      (∀ s : R, s ∈ S ↔ s⁻¹ ∈ S) ∧
      (∀ r, IsGraphAutomorphism adj (leftTranslation r))) →
    IsGraphAutomorphism adj (inversionPermutation) ∧
      inversionPermutation (R := R) (1 : R) = (1 : R) ∧
      (∀ r : R,
        inversionPermutation (R := R) * leftTranslation (R := R) r *
            inversionPermutation (R := R) =
          leftTranslation (R := R) r⁻¹) ∧
      (∀ φ : Equiv.Perm R,
        φ ∈ Subgroup.closure
          (Set.range leftTranslation ∪
            ({inversionPermutation} : Set (Equiv.Perm R))) →
          IsGraphAutomorphism adj φ)

end MathlibPlus.Open.ResearchFormalization
