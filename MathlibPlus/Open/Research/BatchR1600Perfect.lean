import Mathlib

namespace MathlibPlus.Open.Research

def coordinate_pair_hom {D : Type} [Group D] {n : Nat}
    (i j : Fin n) : (Fin n → D) →* D × D :=
  { toFun := fun x => (x i, x j)
    map_one' := by ext <;> simp
    map_mul' := by intro x y; rfl }

def two_surjective {D : Type} [Group D] {n : Nat}
    (M : Subgroup (Fin n → D)) : Prop :=
  2 ≤ n ∧
    ∀ (i j : Fin n), i ≠ j →
      M.map (coordinate_pair_hom i j) = (⊤ : Subgroup (D × D))

/-- Claim 39513: a 2-surjective subgroup of a perfect direct power is full. -/
def perfect_power_two_surjective : Prop :=
  ∀ (D : Type) [Group D] (n : Nat) (M : Subgroup (Fin n → D)),
    commutator D = (⊤ : Subgroup D) →
      two_surjective M → M = (⊤ : Subgroup (Fin n → D))

end MathlibPlus.Open.Research
