import Mathlib

namespace MathlibPlus.Open.R4517

private def directProductMul {A H : Type*} [Add A] [Mul H]
    (x y : A × H) : A × H :=
  (x.1 + y.1, x.2 * y.2)

private def directProductInv {A H : Type*} [Neg A] [Inv H]
    (x : A × H) : A × H :=
  (-x.1, x.2⁻¹)

private def directProductConnectionSet {A H : Type*} [Zero A] [Group H]
    (U : Subgroup H) : Set (A × H) :=
  {x | x.1 ≠ 0} ∪ {x | x.1 = 0 ∧ x.2 ∈ U ∧ x.2 ≠ 1}

private def rightDifferenceStep {A H : Type*} [AddGroup A] [Group H]
    (S : Set (A × H)) (x y : A × H) : Prop :=
  x ≠ y ∧ directProductMul y (directProductInv x) ∈ S

/-- R-4517.1: the displayed direct-product connection set is inverse-closed
and its right-difference Cayley graph is connected. -/
def claim52320 : Prop :=
  ∀ (A H : Type*) [Fintype A] [AddCommGroup A] [Nontrivial A]
    [Fintype H] [Group H],
    ∀ U : Subgroup H, ⊥ < U → U < ⊤ →
      let S := directProductConnectionSet U
      (∀ x, x ∈ S → directProductInv x ∈ S) ∧
        ∀ x y, Relation.ReflTransGen (rightDifferenceStep S) x y

private def naturalTransversal {A H : Type*} (h : H) : Set (A × H) :=
  {x | x.2 = h}

/-- R-4517.3: a one-part right translation is a graph automorphism and
moves the natural A-orbit transversal. -/
def claim52322 : Prop := by
  classical
  exact
    ∀ (A H : Type*) [Fintype A] [AddCommGroup A] [Nontrivial A]
      [Fintype H] [Group H],
      ∀ U : Subgroup H, ⊥ < U → U < ⊤ →
        ∀ (u : H), u ∈ U → u ≠ 1 →
          ∀ (a₀ : A) (h : H),
            let S := directProductConnectionSet U
            let f : A × H → A × H := fun x =>
              if x.1 = a₀ then (x.1, x.2 * u) else x
            Function.Bijective f ∧
              (∀ x y, rightDifferenceStep S x y ↔
                rightDifferenceStep S (f x) (f y)) ∧
              f '' naturalTransversal h ≠ naturalTransversal h

end MathlibPlus.Open.R4517
