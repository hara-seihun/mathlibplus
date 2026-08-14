import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0334

open Set
open scoped BigOperators

universe u

/-- The three distinguished tight coordinates. -/
def tightGround (X : Type u) (t : Fin 3 → X) : Set X := Set.range t

/-- The outside ground, the complement of the tight coordinates. -/
def outsideGround (X : Type u) (t : Fin 3 → X) : Set X := (tightGround X t)ᶜ

/-- The outside trace fiber β(S). -/
def outsideTraceFiber {X : Type u} (F : Set (Set X)) (t : Fin 3 → X)
    (S : Set X) : Set (Set X) :=
  {B | B ⊆ outsideGround X t ∧ S ∪ B ∈ F}

/-- The set-union product of the singleton fibers indexed by a trace. -/
def unionProduct {Y : Type u} (β : Fin 3 → Set (Set Y)) (S : Set (Fin 3)) : Set (Set Y) :=
  {B | ∃ g : {i : Fin 3 // i ∈ S} → Set Y,
      (∀ i, g i ∈ β i.1) ∧ B = ⋃ i, g i}

/-- The product used by the singleton-fiber factorization claim. -/
def outsideSingletonProduct {X : Type u} (F : Set (Set X)) (t : Fin 3 → X)
    (S : Set X) : Set (Set X) :=
  unionProduct (fun i => outsideTraceFiber F t {t i})
    (Set.preimage t S)

/-- Claim 20002: the outside trace fibers have the displayed definition. -/
def claim20002 : Prop :=
  ∀ (X : Type u) (F : Set (Set X)) (t : Fin 3 → X),
    Function.Injective t →
    ∀ S : Set X, S ⊆ tightGround X t →
      outsideTraceFiber F t S =
        {B : Set X | B ⊆ outsideGround X t ∧ S ∪ B ∈ F}

/-- Claim 20003: every nonempty trace fiber is the union product of singleton fibers. -/
def claim20003 : Prop :=
  ∀ (X : Type u) (F : Set (Set X)) (t : Fin 3 → X),
    Function.Injective t →
    ∀ S : Set X, S ⊆ tightGround X t → S.Nonempty →
      outsideTraceFiber F t S = outsideSingletonProduct F t S

/-- Claim 20004: every nonempty trace fiber has empty coordinate intersection. -/
def claim20004 : Prop :=
  ∀ (X : Type u) (F : Set (Set X)) (t : Fin 3 → X),
    Function.Injective t →
    ∀ S : Set X, S ⊆ tightGround X t → S.Nonempty →
      ⋂₀ (outsideTraceFiber F t S) = (∅ : Set X)

/-- Claim 20005: the empty outside set is excluded from every tight singleton fiber. -/
def claim20005 : Prop :=
  ∀ (X : Type u) (F : Set (Set X)) (t : Fin 3 → X),
    Function.Injective t →
    ∀ i : Fin 3, (∅ : Set X) ∉ outsideTraceFiber F t {t i}

/-- The punctured-star collection on an r-coordinate outside ground. -/
def puncturedStar (r : ℕ) : Set (Set (Fin r)) :=
  {(Set.univ : Set (Fin r))} ∪
    {B | ∃ y : Fin r, B = (Set.univ : Set (Fin r)) \ {y}}

/-- The two cases of the fiber in the punctured-star construction. -/
noncomputable def puncturedStarFiber (r : ℕ) (S : Set (Fin 3)) : Set (Set (Fin r)) := by
  classical
  exact if S.Nonempty then puncturedStar r else puncturedStar r ∪ {∅}

/-- Adjoin a tight trace and an outside set as disjoint-sum coordinates. -/
def adjoinTrace {r : ℕ} (S : Set (Fin 3)) (B : Set (Fin r)) : Set (Fin 3 ⊕ Fin r) :=
  Set.image (Sum.inl : Fin 3 → Fin 3 ⊕ Fin r) S ∪
    Set.image (Sum.inr : Fin r → Fin 3 ⊕ Fin r) B

/-- The ordinary family reconstructed by adjoining all traces. -/
def puncturedStarFamily (r : ℕ) : Set (Set (Fin 3 ⊕ Fin r)) :=
  {A | ∃ S : Set (Fin 3), ∃ B : Set (Fin r),
      B ∈ puncturedStarFiber r S ∧ A = adjoinTrace S B}

/-- Union-closedness of a family of sets. -/
def unionClosed {α : Type u} (F : Set (Set α)) : Prop :=
  ∀ ⦃A B : Set α⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

/-- Claim 20010: the punctured-star fibers reconstruct the stated union-closed family. -/
def claim20010 : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    puncturedStarFiber r (∅ : Set (Fin 3)) = puncturedStar r ∪ {∅} ∧
    (∀ S : Set (Fin 3), S.Nonempty →
      puncturedStarFiber r S = puncturedStar r) ∧
    unionClosed (puncturedStarFamily r) ∧
    (∀ S : Set (Fin 3), S.Nonempty →
      puncturedStarFiber r S = unionProduct (fun i => puncturedStarFiber r {i}) S) ∧
    (∀ S : Set (Fin 3), S.Nonempty →
      ⋂₀ (puncturedStarFiber r S) = (∅ : Set (Fin r)))

end MathlibPlus.Open.ResearchFormalization.R0334
