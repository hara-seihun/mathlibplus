import Mathlib

namespace MathlibPlus.Open

abbrev F3Vector (n : ℕ) := Fin n → ZMod 3

abbrev ZeroExtendedSpace (r : ℕ) := F3Vector 6 × F3Vector (r - 6)

def ordinaryUndirectedCayleyAdjacency {α : Type*} [AddGroup α]
    (S : Set α) (x y : α) : Prop :=
  y - x ∈ S

def cayleyConnected {α : Type*} [AddGroup α]
    (S : Set α) (x y : α) : Prop :=
  Relation.ReflTransGen (ordinaryUndirectedCayleyAdjacency S) x y

def identityFreeInverseClosedConnectionSet {α : Type*} [AddGroup α]
    (S : Set α) : Prop :=
  (0 : α) ∉ S ∧ ∀ x, x ∈ S → -x ∈ S

def isCayleyComponentCopy
    {α β : Type*} [AddGroup α] [AddGroup β]
    (ambient : Set α) (rankSix : Set β) (component : Set α) : Prop :=
  ∃ φ : {x // x ∈ component} → β,
    Function.Bijective φ ∧
      ∀ x y : {z // z ∈ component},
        ordinaryUndirectedCayleyAdjacency ambient x.1 y.1 ↔
          ordinaryUndirectedCayleyAdjacency rankSix (φ x) (φ y)

def hasCayleyComponents
    {α β : Type*} [AddGroup α] [AddGroup β]
    (ambient : Set α) (rankSix : Set β)
    (componentCount componentSize degree : ℕ) : Prop :=
  ∃ components : Fin componentCount → Set α,
    (∀ i,
      (components i).Nonempty ∧
      Set.ncard (components i) = componentSize ∧
      (∀ x y, x ∈ components i → y ∈ components i →
        cayleyConnected ambient x y) ∧
      (∀ x, x ∈ components i →
        ∀ y, y ∈ components i ↔ cayleyConnected ambient x y) ∧
      (∀ x, x ∈ components i →
        Set.ncard {y : α |
          y ∈ components i ∧ ordinaryUndirectedCayleyAdjacency ambient x y} = degree) ∧
      isCayleyComponentCopy ambient rankSix (components i)) ∧
    (∀ i j, i ≠ j → Disjoint (components i) (components j)) ∧
    (∀ x, ∃ i, x ∈ components i)

def zeroExtensionSet (S : Set (F3Vector 6)) (r : ℕ) : Set (ZeroExtendedSpace r) :=
  (fun s : F3Vector 6 => (s, (0 : F3Vector (r - 6)))) '' S

def zeroExtensionMap (f : F3Vector 6 ≃ F3Vector 6) (r : ℕ) :
    ZeroExtendedSpace r → ZeroExtendedSpace r :=
  fun p => (f p.1, p.2)

def zeroExtendValency336OrdinaryUndirectedNonCI : Prop :=
  ∀ (S T : Set (F3Vector 6)) (f : F3Vector 6 ≃ F3Vector 6),
    (identityFreeInverseClosedConnectionSet S ∧
      identityFreeInverseClosedConnectionSet T ∧
      Set.ncard S = 336 ∧
      Set.ncard T = 336 ∧
      Submodule.span (ZMod 3) S = ⊤ ∧
      Submodule.span (ZMod 3) T = ⊤ ∧
      (∀ x y,
        ordinaryUndirectedCayleyAdjacency S x y ↔
          ordinaryUndirectedCayleyAdjacency T (f x) (f y)) ∧
      (∀ g : F3Vector 6 ≃ₗ[ZMod 3] F3Vector 6, g '' S ≠ T)) →
    ∀ r : ℕ, 6 ≤ r →
      let S_r := zeroExtensionSet S r
      let T_r := zeroExtensionSet T r
      identityFreeInverseClosedConnectionSet S_r ∧
      identityFreeInverseClosedConnectionSet T_r ∧
      Set.ncard S_r = 336 ∧
      Set.ncard T_r = 336 ∧
      Function.Bijective (zeroExtensionMap f r) ∧
      (∀ x y,
        ordinaryUndirectedCayleyAdjacency S_r x y ↔
          ordinaryUndirectedCayleyAdjacency T_r
            (zeroExtensionMap f r x) (zeroExtensionMap f r y)) ∧
      (∀ g : ZeroExtendedSpace r ≃ₗ[ZMod 3] ZeroExtendedSpace r,
        g '' S_r ≠ T_r) ∧
      hasCayleyComponents S_r S (3 ^ (r - 6)) 729 336 ∧
      hasCayleyComponents T_r T (3 ^ (r - 6)) 729 336

end MathlibPlus.Open
