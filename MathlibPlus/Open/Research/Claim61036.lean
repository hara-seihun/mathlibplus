import Mathlib

namespace MathlibPlus.Open.Research.Claim61036

abbrev A := Fin 4 → ZMod 2
abbrev B := ZMod 3 × ZMod 3
abbrev G := A × B

def bitVector (n : Nat) : A :=
  fun i => (n / 2 ^ i.val % 2 : ZMod 2)

def bCode (b : B) : Nat :=
  b.1.val + 3 * b.2.val

def columnCode (b : B) (i : Fin 4) : Nat :=
  match bCode b, i.val with
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, 2 => 4
  | 0, 3 => 8
  | 1, 0 => 5
  | 1, 1 => 15
  | 1, 2 => 11
  | 1, 3 => 13
  | 2, 0 => 10
  | 2, 1 => 14
  | 2, 2 => 12
  | 2, 3 => 3
  | 3, 0 => 3
  | 3, 1 => 6
  | 3, 2 => 10
  | 3, 3 => 2
  | 4, 0 => 12
  | 4, 1 => 13
  | 4, 2 => 6
  | 4, 3 => 14
  | 5, 0 => 14
  | 5, 1 => 15
  | 5, 2 => 12
  | 5, 3 => 10
  | 6, 0 => 7
  | 6, 1 => 14
  | 6, 2 => 6
  | 6, 3 => 10
  | 7, 0 => 13
  | 7, 1 => 9
  | 7, 2 => 10
  | 7, 3 => 15
  | 8, 0 => 8
  | 8, 1 => 15
  | 8, 2 => 3
  | 8, 3 => 14
  | _, _ => 0

def shiftCode (b : B) : Nat :=
  match bCode b with
  | 0 => 0
  | 1 => 14
  | 2 => 10
  | 3 => 15
  | 4 => 9
  | 5 => 9
  | 6 => 9
  | 7 => 5
  | 8 => 4
  | _ => 0

def linearPart (b : B) (a : A) : A :=
  fun i => ∑ j : Fin 4, a j • bitVector (columnCode b j) i

def shiftPart (b : B) : A :=
  bitVector (shiftCode b)

def explicitF (x : G) : G :=
  (linearPart x.2 x.1 + shiftPart x.2, x.2)

def linearAutomorphismTable (b : B) : Prop :=
  ∃ L : A ≃ₗ[ZMod 2] A, ∀ a : A, L a = linearPart b a

def pointedPermutation : Prop :=
  explicitF 0 = 0 ∧ Function.Bijective explicitF

def fixedSet (α : G ≃+ G) : Set G :=
  {x | α.symm (explicitF x) = x}

def setDifference (S T : Set G) : Set G :=
  {z | ∃ x ∈ S, ∃ y ∈ T, z = x - y}

def escapesFixedDifferenceCover : Prop :=
  ∀ α : G ≃+ G,
    setDifference (fixedSet α) (fixedSet α) ≠ Set.univ

def inverseAtom (D : Finset G) : Prop :=
  ∃ d : G, d ≠ 0 ∧ D = {d, -d}

def edgeSet (D : Finset G) : Set (Finset G) :=
  {e | ∃ x : G, ∃ d : G, d ∈ D ∧ e = {x, x + d}}

def edgeMap (q : G → G) (e : Finset G) : Finset G :=
  e.image q

def atomIncidence (D D' : Finset G) : Prop :=
  inverseAtom D ∧ inverseAtom D' ∧
    ∃ e : Finset G, e ∈ edgeSet D ∧ edgeMap explicitF e ∈ edgeSet D'

def Node := Sum (Finset G) (Finset G)

def validNode : Node → Prop
  | Sum.inl D => inverseAtom D
  | Sum.inr D => inverseAtom D

def incidenceAdj : Node → Node → Prop
  | Sum.inl D, Sum.inr D' => atomIncidence D D'
  | Sum.inr D', Sum.inl D => atomIncidence D D'
  | _, _ => False

def connected (u v : Node) : Prop :=
  Relation.ReflTransGen incidenceAdj u v

def fiveComponentRepresentatives (reps : Fin 5 → Node) : Prop :=
  (∀ i : Fin 5, validNode (reps i)) ∧
  (∀ v : Node, validNode v → ∃ i : Fin 5, connected (reps i) v) ∧
  (∀ i j : Fin 5, connected (reps i) (reps j) ↔ i = j) ∧
  (∀ i : Fin 5,
    ∃ D : Finset G, ∃ D' : Finset G,
      inverseAtom D ∧ inverseAtom D' ∧
      connected (reps i) (Sum.inl D) ∧
      connected (reps i) (Sum.inr D'))

def involutionAtom (D : Finset G) : Prop :=
  ∃ a : A, a ≠ 0 ∧ D = {((a, 0) : G), -((a, 0) : G)}

def projectiveLine (ell : Finset B) : Prop :=
  ∃ b : B, b ≠ 0 ∧ ell = {b, -b}

def lineAtom (ell : Finset B) (D : Finset G) : Prop :=
  ∃ a : A, ∃ b : B, b ∈ ell ∧ D = {((a, b) : G), -((a, b) : G)}

def componentLabelStructure : Prop :=
  Nat.card {D : Finset G // inverseAtom D ∧ involutionAtom D} = 15 ∧
  Nat.card {ell : Finset B // projectiveLine ell} = 4 ∧
  (∀ ell : Finset B, projectiveLine ell →
    Nat.card {D : Finset G // inverseAtom D ∧ lineAtom ell D} = 16) ∧
  ∃ reps : Fin 5 → Node,
    fiveComponentRepresentatives reps ∧
    (∀ D : Finset G, inverseAtom D →
      (connected (reps 0) (Sum.inl D) ↔ involutionAtom D) ∧
      (connected (reps 0) (Sum.inr D) ↔ involutionAtom D)) ∧
    (∀ ell : Finset B, projectiveLine ell →
      ∃ i : Fin 4,
        (∀ D : Finset G, inverseAtom D →
          (connected (reps (Fin.succ i)) (Sum.inl D) ↔ lineAtom ell D) ∧
          (connected (reps (Fin.succ i)) (Sum.inr D) ↔ lineAtom ell D))) ∧
    (∀ D D' : Finset G, inverseAtom D → inverseAtom D' →
      connected (Sum.inl D) (Sum.inr D') →
      ∀ E : Finset G, inverseAtom E →
        (connected (Sum.inl D) (Sum.inl E) ↔
          connected (Sum.inr D') (Sum.inr E)))

def selectedNode (U : Set (Finset G)) : Node → Prop
  | Sum.inl D => D ∈ U
  | Sum.inr D => D ∈ U

def unionOfComponents (U : Set (Finset G)) : Prop :=
  (∀ D : Finset G, D ∈ U → inverseAtom D) ∧
  (∀ u v : Node, validNode u → validNode v → connected u v →
    (selectedNode U u ↔ selectedNode U v))

def connectionSet (U : Set (Finset G)) : Set G :=
  {g | ∃ D : Finset G, D ∈ U ∧ g ∈ D}

def identityFree (S : Set G) : Prop :=
  0 ∉ S

def inverseClosed (S : Set G) : Prop :=
  ∀ x : G, x ∈ S → -x ∈ S

def cayleyRelation (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyRelationIso (S T : Set G) (q : G → G) : Prop :=
  Function.Bijective q ∧
    ∀ x y : G, cayleyRelation S x y ↔ cayleyRelation T (q x) (q y)

def identityAutomorphismShadow (S T : Set G) : Prop :=
  Set.image (AddEquiv.refl G) S = T

def componentConsequence : Prop :=
  ∀ U : Set (Finset G), unionOfComponents U →
    identityFree (connectionSet U) ∧
    inverseClosed (connectionSet U) ∧
    cayleyRelationIso (connectionSet U) (connectionSet U) explicitF ∧
    identityAutomorphismShadow (connectionSet U) (connectionSet U)

/-- Claim 61036: the explicit fibre-affine permutation escapes every
fixed-difference-cover normalization, while its complete inverse-atom
incidence system has five harmless equal-label components. -/
def claim61036 : Prop :=
  (∀ b : B, linearAutomorphismTable b) ∧
  pointedPermutation ∧
  escapesFixedDifferenceCover ∧
  componentLabelStructure ∧
  componentConsequence

end MathlibPlus.Open.Research.Claim61036
