import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.TransitivityModule

noncomputable def rightRegularSubgroup (H : Type*) [Group H] :
    Subgroup (Equiv.Perm H) :=
  Subgroup.closure (Set.range (fun h : H => Equiv.mulRight h))

noncomputable def pointStabilizerOrbits (H : Type*) [Group H]
    (G : Subgroup (Equiv.Perm H)) : Set (Set H) :=
  Set.range (fun x : H =>
    MulAction.orbit (MulAction.stabilizer G (1 : H)) x)

noncomputable def simpleQuantity (H : Type*) [Fintype H] [Group H]
    (T : Set H) : MonoidAlgebra ℚ H :=
  Finset.sum
    ((Set.Finite.subset (Set.finite_univ : (Set.univ : Set H).Finite)
      (Set.subset_univ T)).toFinset)
    (fun t => MonoidAlgebra.single t 1)

noncomputable def transitivityModule (H : Type*) [Fintype H] [Group H]
    (G : Subgroup (Equiv.Perm H)) : Submodule ℚ (MonoidAlgebra ℚ H) :=
  Submodule.span ℚ (Set.image (simpleQuantity H) (pointStabilizerOrbits H G))

def claim_28081 : Prop :=
  ∀ (H : Type*) [Fintype H] [Group H]
    (G : Subgroup (Equiv.Perm H)),
    rightRegularSubgroup H ≤ G →
      let e : H := 1
      let Gₑ := MulAction.stabilizer G e
      let orbit := fun x : H => MulAction.orbit Gₑ x
      ∃ r : ℕ, ∃ T : Fin (r + 1) → Set H,
        T 0 = ({e} : Set H) ∧
        (∀ i, ∃ x, T i = orbit x) ∧
        (∀ x, ∃ i, orbit x = T i) ∧
        (⋃ i, T i) = Set.univ ∧
        (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
        Set.range T = Set.range orbit

def claim_28082 : Prop :=
  ∀ (H : Type*) [Fintype H] [Group H]
    (G : Subgroup (Equiv.Perm H)) (T : Set H),
    simpleQuantity H T =
        Finset.sum
          ((Set.Finite.subset (Set.finite_univ : (Set.univ : Set H).Finite)
            (Set.subset_univ T)).toFinset)
          (fun t => MonoidAlgebra.single t 1) ∧
      transitivityModule H G =
        Submodule.span ℚ (Set.image (simpleQuantity H) (pointStabilizerOrbits H G))

end MathlibPlus.Open.Research.TransitivityModule
