import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Batch01

noncomputable section

/-- The alternating subgroup on four points, used as the concrete carrier for `A₄`. -/
def alternatingFourSubgroup : Subgroup (Equiv.Perm (Fin 4)) :=
  (Equiv.Perm.sign).ker

abbrev A4 := alternatingFourSubgroup
abbrev C5 := Multiplicative (ZMod 5)
abbrev G54 := C5 × A4

instance : Fintype A4 := Fintype.ofFinite A4
instance : Fintype C5 := Fintype.ofFinite C5
instance : Fintype G54 := Fintype.ofFinite G54

/-- Elementary group data for `A₄`: trivial centre, four Sylow 3-subgroups,
 and twenty-four automorphisms. -/
def claim28206 : Prop :=
  (∀ x : A4, x ∈ Subgroup.center A4 ↔ x = 1) ∧
    Nat.card {H : Subgroup A4 // Nat.card H = 3} = 4 ∧
    Nat.card (MulAut A4) = 24

/-- The direct-product automorphism description and the factor counts for
 `C₅ × A₄`. -/
def claim28208 : Prop :=
  (∀ f : C5 →* A4, ∀ x, f x = 1) ∧
    (∀ f : A4 →* C5, ∀ x, f x = 1) ∧
    Nonempty (MulAut G54 ≃* (MulAut C5 × MulAut A4)) ∧
    Nat.card (MulAut C5) = 4 ∧
    Nat.card (MulAut A4) = 24 ∧
    Nat.card (MulAut G54) = 96

/-- The inverse atom represented by a nonidentity group element. -/
noncomputable def inverseAtomSet {G : Type} [Group G] (g : G) : Finset G := by
  classical
  exact {g, g⁻¹}

def inverseAtoms (G : Type) [Group G] [Fintype G] : Type :=
  {S : Finset G // ∃ g : G, g ≠ 1 ∧ S = inverseAtomSet g}

/-- Faithfulness of the automorphism action on the inverse atoms. -/
def claim28210 : Prop := by
  classical
  exact
    Nat.card (inverseAtoms G54) = 31 ∧
      Nat.card (MulAut G54) = 96 ∧
      (∀ φ : MulAut G54,
        (∀ S : inverseAtoms G54,
          S.1.image (fun x => φ x) = S.1) → φ = 1)

/-- Normalized displacements and their generated additive subgroup. -/
def normalizedDisplacement {B : Type} [AddGroup B]
    (p : Equiv.Perm B) : AddSubgroup B :=
  AddSubgroup.closure (Set.range (fun t : B => t - p t + p 0))

/-- The definition of the displacement subgroup of a fibre permutation. -/
def claim28258 : Prop :=
  ∀ {B : Type} [AddGroup B] (p : Equiv.Perm B),
    normalizedDisplacement p =
      AddSubgroup.closure (Set.range (fun t : B => t - p t + p 0))

abbrev B3 := ZMod 3 × ZMod 3

def standardTernaryLine : AddSubgroup B3 :=
  AddSubgroup.prod (⊤ : AddSubgroup (ZMod 3)) (⊥ : AddSubgroup (ZMod 3))

/-- A concrete additive coset, avoiding a choice of quotient presentation. -/
def additiveCoset (x : B3) (L : AddSubgroup B3) : Set B3 :=
  {y | y - x ∈ L}

/-- Proper displacement sums in `C₃²` lie in one line, and every line can be
 normalized to the first coordinate line by a linear automorphism. -/
def claim28267 : Prop :=
  ∀ p r : Equiv.Perm B3,
    normalizedDisplacement p ⊔ normalizedDisplacement r < (⊤ : AddSubgroup B3) →
      ∃ L : AddSubgroup B3,
        Nat.card L = 3 ∧
          L < (⊤ : AddSubgroup B3) ∧
          normalizedDisplacement p ≤ L ∧
          normalizedDisplacement r ≤ L ∧
          ∃ e : B3 ≃+ B3,
            e '' (L : Set B3) = (standardTernaryLine : Set B3)

/-- Displacements lie in a line exactly when the permutation is a translation
 on the corresponding cosets. -/
def claim28268 : Prop :=
  ∀ (q : Equiv.Perm B3) (L : AddSubgroup B3),
    normalizedDisplacement q ≤ L ↔
      ∀ t : B3,
        additiveCoset (q t) L = additiveCoset (t + q 0) L

/-- Exact permutation counts for the four ternary lines and their spans. -/
def claim28269 : Prop :=
  Nat.card (Equiv.Perm B3) = Nat.factorial 9 ∧
    Nat.card {L : AddSubgroup B3 // Nat.card L = 3} = 4 ∧
    Nat.card {p : Equiv.Perm B3 // normalizedDisplacement p = ⊥} = 9 ∧
    (∀ p : Equiv.Perm B3,
      normalizedDisplacement p = ⊥ ↔ ∃ c : B3, ∀ t, p t = t + c) ∧
    Nat.card {p : Equiv.Perm B3 // normalizedDisplacement p = ⊤} = 360315 ∧
    (∀ L : AddSubgroup B3, Nat.card L = 3 →
      Nat.card {p : Equiv.Perm B3 // normalizedDisplacement p = L} = 639 ∧
        Nat.card {p : Equiv.Perm B3 // normalizedDisplacement p ≤ L} = 648)

end
end MathlibPlus.Open.ResearchFormalization.Batch01
