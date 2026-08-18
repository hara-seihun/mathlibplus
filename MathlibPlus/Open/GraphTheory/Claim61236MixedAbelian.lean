import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Identity-free inverse-closed connection sets for an additive Cayley graph. -/
def inverseClosedIdentityFree61236 {G : Type*} [AddGroup G]
    (S : Set G) : Prop :=
  0 ∉ S ∧ ∀ x : G, x ∈ S ↔ -x ∈ S

/-- An ordinary additive Cayley graph isomorphism together with its pointed
normalization. -/
def pointedAdditiveCayleyIso61236 {G : Type*} [AddGroup G]
    (S T : Set G) (f : G ≃ G) : Prop :=
  f 0 = 0 ∧
    ∀ x y : G,
      (SimpleGraph.addCayley S).Adj x y ↔
        (SimpleGraph.addCayley T).Adj (f x) (f y)

/-- The strict fibre-density threshold, with the floor in the numerator. -/
def elementaryFibreThreshold61236 {V : Type*}
    (p : ℕ) (K : Set V) : Prop :=
  (Set.ncard K : ℚ) >
    ((p / 2 : ℕ) : ℚ) / (p : ℚ) * (Nat.card V : ℚ)

/-- The additive difference set used in the sharpness clause. -/
def additiveDifferenceSet61236 {V : Type*} [AddGroup V]
    (K : Set V) : Set V :=
  {h | ∃ x ∈ K, ∃ y ∈ K, y - x = h}

/-- Main fixed-fibre shadow theorem, together with its ternary and first
post-order-108 specializations and the stated sharpness witness. -/
def claim61236_mixed_abelian_elementary_base_fixed_fibre_shadow : Prop :=
  (∀ (p s : ℕ), Nat.Prime p → 1 ≤ s →
    let V := Fin s → ZMod p
    ∀ (A : Type*) [AddCommGroup A] [Fintype A],
      let G := A × V
      ∀ (S T : Set G) (f : G ≃ G) (α : G ≃+ G) (K : Set V),
        inverseClosedIdentityFree61236 S →
        inverseClosedIdentityFree61236 T →
        pointedAdditiveCayleyIso61236 S T f →
        (∀ a : A, ∀ k : V, k ∈ K → f (a, k) = α (a, k)) →
        elementaryFibreThreshold61236 p K →
        α '' S = T) ∧
  (∀ (s : ℕ), 1 ≤ s →
    let V := Fin s → ZMod 3
    ∀ (A : Type*) [AddCommGroup A] [Fintype A],
      let G := A × V
      ∀ (S T : Set G) (f : G ≃ G) (α : G ≃+ G) (K : Set V),
        inverseClosedIdentityFree61236 S →
        inverseClosedIdentityFree61236 T →
        pointedAdditiveCayleyIso61236 S T f →
        (∀ a : A, ∀ k : V, k ∈ K → f (a, k) = α (a, k)) →
        (Set.ncard K : ℚ) > (1 : ℚ) / 3 * (Nat.card V : ℚ) →
        α '' S = T) ∧
  (let A := Fin 4 → ZMod 2
   let V := Fin 2 → ZMod 3
   let G := A × V
   ∀ (S T : Set G) (f : G ≃ G) (α : G ≃+ G) (K : Set V),
      inverseClosedIdentityFree61236 S →
      inverseClosedIdentityFree61236 T →
      pointedAdditiveCayleyIso61236 S T f →
      (∀ a : A, ∀ k : V, k ∈ K → f (a, k) = α (a, k)) →
      4 ≤ Set.ncard K →
      α '' S = T) ∧
  (let V := Fin 2 → ZMod 3
   let L : Set V := {x | x 1 = 0}
   Set.ncard L = 3 ∧
     additiveDifferenceSet61236 L ≠ Set.univ)

end MathlibPlus.Open.GraphTheory
