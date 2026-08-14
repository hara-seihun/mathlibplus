import Mathlib

namespace MathlibPlus.Open.Research

/-- The connection relation for a Cayley graph on `ZMod 9`. -/
def cayleyAdjacency (S : Set (ZMod 9)) (x y : ZMod 9) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Isomorphism of the explicit Cayley adjacency relations. -/
def cayleyGraphIsomorphic (S T : Set (ZMod 9)) : Prop :=
  ∃ e : ZMod 9 ≃ ZMod 9, ∀ x y : ZMod 9,
    cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

def inverseClosed (S : Set (ZMod 9)) : Prop :=
  ∀ x : ZMod 9, x ∈ S ↔ -x ∈ S

def nonzeroConnectionSet (S : Set (ZMod 9)) : Prop :=
  (∀ x : ZMod 9, x ∈ S → x ≠ 0) ∧ inverseClosed S

def unitsMod9 : Set (ZMod 9) := {1, 2, 4, 5, 7, 8}

def scalarSetImage (u : ZMod 9) (S : Set (ZMod 9)) : Set (ZMod 9) :=
  {y | ∃ x, x ∈ S ∧ y = u * x}

def undirectedCIGroupZMod9 : Prop :=
  ∀ S T : Set (ZMod 9),
    nonzeroConnectionSet S → nonzeroConnectionSet T →
      (cayleyGraphIsomorphic S T ↔
        ∃ u : ZMod 9, u ∈ unitsMod9 ∧ T = scalarSetImage u S)

abbrev FourBits := Fin 4 → Bool

def bitVector (b₀ b₁ b₂ b₃ : Bool) : FourBits :=
  fun i =>
    if i = (0 : Fin 4) then b₀
    else if i = (1 : Fin 4) then b₁
    else if i = (2 : Fin 4) then b₂
    else b₃

def P₁ : Set (ZMod 9) := {1, 8}
def P₂ : Set (ZMod 9) := {2, 7}
def P₄ : Set (ZMod 9) := {4, 5}
def P₃ : Set (ZMod 9) := {3, 6}

def bitConnection (b : FourBits) : Set (ZMod 9) :=
  (if b 0 = true then P₁ else ∅) ∪
  (if b 1 = true then P₂ else ∅) ∪
  (if b 2 = true then P₄ else ∅) ∪
  (if b 3 = true then P₃ else ∅)

def graphIsomorphismFiber (b : FourBits) : Set FourBits :=
  {c | cayleyGraphIsomorphic (bitConnection b) (bitConnection c)}

def additiveAutomorphismImage (e : ZMod 9 ≃+ ZMod 9) (S : Set (ZMod 9)) : Set (ZMod 9) :=
  e '' S

def automorphismOrbitFiber (b : FourBits) : Set FourBits :=
  {c | ∃ e : ZMod 9 ≃+ ZMod 9,
    bitConnection c = additiveAutomorphismImage e (bitConnection b)}

def fiber0000 : Set FourBits := {bitVector false false false false}

def fiber1000 : Set FourBits :=
  {bitVector true false false false,
   bitVector false true false false,
   bitVector false false true false}

def fiber1100 : Set FourBits :=
  {bitVector true true false false,
   bitVector true false true false,
   bitVector false true true false}

def fiber0001 : Set FourBits := {bitVector false false false true}

def fiber1001 : Set FourBits :=
  {bitVector true false false true,
   bitVector false true false true,
   bitVector false false true true}

def fiber1101 : Set FourBits :=
  {bitVector true true false true,
   bitVector true false true true,
   bitVector false true true true}

def fiber1110 : Set FourBits := {bitVector true true true false}
def fiber1111 : Set FourBits := {bitVector true true true true}

def listedGraphIsomorphismFibers : Set (Set FourBits) :=
  {fiber0000, fiber1000, fiber1100, fiber0001,
   fiber1001, fiber1101, fiber1110, fiber1111}

def connectionSetEncoding : Prop :=
  ∀ S : Set (ZMod 9), nonzeroConnectionSet S →
    ∃! b : FourBits, bitConnection b = S

/-- The admitted CI classification and its complete eight fiber description. -/
def claim59621 : Prop :=
  undirectedCIGroupZMod9 ∧
    connectionSetEncoding ∧
    (∀ b : FourBits, graphIsomorphismFiber b = automorphismOrbitFiber b) ∧
    Set.range graphIsomorphismFiber = listedGraphIsomorphismFibers

end MathlibPlus.Open.Research
