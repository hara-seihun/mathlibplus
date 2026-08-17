import MathlibPlus.Open.Research.R2218Setup
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace MathlibPlus.Open.ResearchFormalization.R2218Claims

noncomputable section
open Classical

open MathlibPlus.Open.Research

abbrev R2218Field := R2218F7
abbrev R2218Vec := R2218Vector
abbrev R2218Group := R2218G
abbrev R2218PlanarVector := Fin 2 → R2218Field
abbrev R2218Direction := Fin 8

/-- The layer-zero copy of the vector subgroup. -/
def vSet : Set R2218Group :=
  {g | g.2 = 0}

/-- The central z-axis in the layer-zero vector copy. -/
def zSet : Set R2218Group :=
  {g | g.2 = 0 ∧ g.1 0 = 0 ∧ g.1 1 = 0}

/-- The identity of the displayed coordinate carrier. -/
def groupIdentity : R2218Group := (0, 0)

/-- The planar coordinates of a vector in `F₇³`. -/
def planarCoordinates (v : R2218Vec) : R2218PlanarVector :=
  fun i => v i.castSucc

/-- Canonical representatives for the eight points of `P¹(F₇)`: the seven
finite slopes followed by the vertical direction. -/
def directionVector (l : R2218Direction) : R2218PlanarVector :=
  if l.val < 7 then
    fun i => if i = 0 then 1 else (l.val : R2218Field)
  else
    fun i => if i = 0 then 0 else 1

def directionLine (l : R2218Direction) :
    Submodule R2218Field R2218PlanarVector :=
  Submodule.span R2218Field ({directionVector l} : Set R2218PlanarVector)

/-- The rank-two plane spanned by a projective xy-direction and the z-axis. -/
def planeSet (l : R2218Direction) : Set R2218Group :=
  {g | g.2 = 0 ∧ planarCoordinates g.1 ∈ directionLine l}

/-- The ten displayed quotient components as connection-element sets. -/
def qSet : Set R2218Group := Set.univ \ vSet

def directionComponent (l : R2218Direction) : Set R2218Group :=
  planeSet l \ zSet

def zComponent : Set R2218Group := zSet \ {groupIdentity}

/-- The four standard generators (three vector basis elements and `c`). -/
def standardBasis (j : Fin 3) : R2218Vec :=
  fun k => if k = j then 1 else 0

def regularGenerator (i : Fin 4) : R2218Group :=
  if h : i.val < 3 then
    r2218EmbedV (standardBasis ⟨i.val, h⟩)
  else
    r2218C

/-- The right-regular difference of two vertices. -/
def rightDifference (x y : R2218Group) : R2218Group :=
  r2218Mul (r2218Inv x) y

/-- The inverse pair represented by a nonidentity connection element. -/
def inversePair (g : R2218Group) : Finset R2218Group :=
  {g, r2218Inv g}

abbrev Atom :=
  {A : Finset R2218Group // ∃ g : R2218Group,
    g ≠ groupIdentity ∧ A = inversePair g}

/-- Applying a conjugated generator to a source edge and reading the image
edge back in right-regular coordinates. -/
def conjugatedGeneratorImage (i : Fin 4) (x : R2218Group) : R2218Group :=
  r2218T (regularGenerator i) x

def atomTransition (A B : Atom) : Prop :=
  ∃ g : R2218Group, g ≠ groupIdentity ∧ A.1 = inversePair g ∧
    ∃ x : R2218Group, ∃ i : Fin 4,
      B.1 = inversePair
        (rightDifference
          (conjugatedGeneratorImage i x)
          (conjugatedGeneratorImage i (r2218Mul x g)))

def atomAdjacency (A B : Atom) : Prop :=
  atomTransition A B ∨ atomTransition B A

def sameComponent (A B : Atom) : Prop :=
  Relation.ReflTransGen atomAdjacency A B

def atomComponent (A : Atom) : Finset Atom :=
  Finset.univ.filter (sameComponent A)

def componentFamily : Finset (Finset Atom) :=
  Finset.univ.image atomComponent

def atomsInside (X : Set R2218Group) : Finset Atom :=
  Finset.univ.filter (fun A => ∀ g ∈ A.1, g ∈ X)

/-- The concrete fusion obtained from a selected family of quotient
components. -/
def fusionFromComponents (C : Finset (Finset Atom)) : Set R2218Group :=
  {g | ∃ K ∈ C, ∃ A ∈ K, g ∈ A.1}

def inverseClosedSet (S : Set R2218Group) : Prop :=
  ∀ g : R2218Group, g ∈ S ↔ r2218Inv g ∈ S

def ordinaryFusion (S : Set R2218Group) : Prop :=
  inverseClosedSet S ∧
    ∃ C : Finset (Finset Atom), C ⊆ componentFamily ∧
      S = fusionFromComponents C

/-- Kernel partitions are the coset partitions with rank-two plane kernels. -/
def kernelPartitionRelation (l : R2218Direction)
    (v w : R2218Vec) : Prop :=
  planarCoordinates v - planarCoordinates w ∈ directionLine l

def shearPreservesKernelPartition (l : R2218Direction) : Prop :=
  ∀ v w : R2218Vec,
    kernelPartitionRelation l (r2218Shear v) (r2218Shear w) ↔
      kernelPartitionRelation l v w

def xyChart : Set R2218Vec :=
  {v | v 2 = 0}

def shearBreaksXYChart : Prop :=
  ∃ v : R2218Vec, v ∈ xyChart ∧ r2218Shear v ∉ xyChart

/-- Bits select the large quotient component and the z-axis component. -/
def selectedDirectionComponents (M : Finset R2218Direction) : Set R2218Group :=
  {g | ∃ l ∈ M, g ∈ directionComponent l}

def fusionSet (epsilon eta : Bool) (M : Finset R2218Direction) :
    Set R2218Group :=
  (if epsilon then qSet else ∅) ∪
    selectedDirectionComponents M ∪
      (if eta then zComponent else ∅)

abbrev FusionParameter := Bool × (Finset R2218Direction × Bool)

def fusionParameterSet (p : FusionParameter) : Set R2218Group :=
  fusionSet p.1 p.2.2 p.2.1

def complementRepresentatives : Finset FusionParameter :=
  Finset.univ.filter (fun p => p.1 = true)

def directionComplement (M : Finset R2218Direction) :
    Finset R2218Direction :=
  Finset.univ \ M

def nonidentitySet : Set R2218Group := Set.univ \ {groupIdentity}

def fusionComplement (S : Set R2218Group) : Set R2218Group :=
  nonidentitySet \ S

abbrev KernelParameter := Finset R2218Direction × Bool

def kernelConnection (M : Finset R2218Direction) (eta : Bool) :
    Set R2218Vec :=
  {v | r2218EmbedV v ∈
    selectedDirectionComponents M ∪ (if eta then zComponent else ∅)}

def kernelGraph (M : Finset R2218Direction) (eta : Bool) :
    SimpleGraph R2218Vec :=
  SimpleGraph.fromRel (fun x y =>
    x ≠ y ∧ y - x ∈ kernelConnection M eta)

def kernelConnected (M : Finset R2218Direction) (eta : Bool) : Prop :=
  (kernelGraph M eta).Connected

def kernelNontrivial (M : Finset R2218Direction) (eta : Bool) : Prop :=
  kernelGraph M eta ≠ ⊥ ∧ kernelGraph M eta ≠ ⊤

def fullGraph (epsilon eta : Bool) (M : Finset R2218Direction) :
    SimpleGraph R2218Group :=
  SimpleGraph.fromRel (fun x y =>
    x ≠ y ∧ rightDifference x y ∈ fusionSet epsilon eta M)

def completeJoinLift (M : Finset R2218Direction) (eta : Bool) :
    SimpleGraph R2218Group :=
  SimpleGraph.fromRel (fun x y =>
    x ≠ y ∧
      (x.2 ≠ y.2 ∨ (kernelGraph M eta).Adj x.1 y.1))

def disjointUnionLift (M : Finset R2218Direction) (eta : Bool) :
    SimpleGraph R2218Group :=
  SimpleGraph.fromRel (fun x y =>
    x ≠ y ∧ x.2 = y.2 ∧ (kernelGraph M eta).Adj x.1 y.1)

def kernelValency (M : Finset R2218Direction) (eta : Bool) : ℕ :=
  Set.ncard ((kernelGraph M eta).neighborSet 0)

/-- The exact graph carrier for a kernel fusion is the labeled graph relation
on the fixed vector carrier; distinctness here is graph equality, not graph
isomorphism. -/
def exactKernelGraphTypes : Finset (SimpleGraph R2218Vec) :=
  Finset.univ.image (fun p : KernelParameter => kernelGraph p.1 p.2)

def exactKernelGraphTypeCensus : Prop :=
  exactKernelGraphTypes.card = 512 ∧
    (∀ p q : KernelParameter,
      kernelGraph p.1 p.2 = kernelGraph q.1 q.2 → p = q)

/-- Claim 43450: the concrete inverse-pair quotient has the ten displayed
components, their exact element/atom sizes, and the stated preserved and
broken partitions. -/
def exactUnorderedQuotientComponents_claim43450 : Prop :=
  Fintype.card R2218Group = 1029 ∧
    Fintype.card Atom = 514 ∧
    Fintype.card R2218Direction = 8 ∧
    componentFamily.card = 10 ∧
    Set.ncard qSet = 686 ∧
    (∀ l : R2218Direction, Set.ncard (directionComponent l) = 42) ∧
    Set.ncard zComponent = 6 ∧
    atomsInside qSet ∈ componentFamily ∧
    (∀ l : R2218Direction,
      atomsInside (directionComponent l) ∈ componentFamily) ∧
    atomsInside zComponent ∈ componentFamily ∧
    (atomsInside qSet).card = 343 ∧
    (∀ l : R2218Direction,
      (atomsInside (directionComponent l)).card = 21) ∧
    (atomsInside zComponent).card = 3 ∧
    componentFamily =
      {atomsInside qSet} ∪
        (Finset.univ.image (fun l : R2218Direction =>
          atomsInside (directionComponent l))) ∪
          {atomsInside zComponent} ∧
    (∀ l : R2218Direction, shearPreservesKernelPartition l) ∧
    shearBreaksXYChart

/-- Claim 43451: all ordinary inverse-closed fusions, the complement involution,
the kernel census, and the two three-layer lifts. -/
def completeFusionCensus_claim43451 : Prop :=
  (∀ S : Set R2218Group,
    ordinaryFusion S ↔
      ∃! p : FusionParameter, S = fusionParameterSet p) ∧
  Fintype.card FusionParameter = 1024 ∧
  complementRepresentatives.card = 512 ∧
  (∀ epsilon eta : Bool, ∀ M : Finset R2218Direction,
    fusionComplement (fusionSet epsilon eta M) =
      fusionSet (!epsilon) (!eta) (directionComplement M)) ∧
  Fintype.card KernelParameter = 512 ∧
  (∀ M : Finset R2218Direction, ∀ eta : Bool,
    kernelValency M eta = 42 * M.card + (if eta then 6 else 0) ∧
    (kernelConnected M eta ↔ 2 ≤ M.card)) ∧
  Fintype.card {p : KernelParameter // kernelConnected p.1 p.2} = 494 ∧
  Fintype.card {p : KernelParameter // kernelNontrivial p.1 p.2} = 510 ∧
  Fintype.card {p : KernelParameter //
    kernelConnected p.1 p.2 ∧ kernelNontrivial p.1 p.2} = 493 ∧
  exactKernelGraphTypeCensus ∧
  (∀ M : Finset R2218Direction, ∀ eta : Bool,
    fullGraph true eta M = completeJoinLift M eta ∧
    fullGraph false eta M = disjointUnionLift M eta)

/-- A concrete map with a named inverse preserves adjacency in a graph. -/
def graphAutomorphismWithInverse (Γ : SimpleGraph R2218Group)
    (f finv : R2218Group → R2218Group) : Prop :=
  (∀ x, finv (f x) = x ∧ f (finv x) = x) ∧
    ∀ x y, Γ.Adj x y ↔ Γ.Adj (f x) (f y)

def preservesComponent (X : Set R2218Group) : Prop :=
  ∀ x : R2218Group, x ∈ X ↔ r2218F x ∈ X

/-- Claim 43452: the concrete layerwise shear is component-preserving and is
a graph automorphism for every displayed fusion, and conjugates the literal
right-regular maps to their `F`-conjugates. -/
def explicitFullGraphConjugator_claim43452 : Prop :=
  Fintype.card R2218Group = 1029 ∧
  preservesComponent qSet ∧
  (∀ l : R2218Direction,
    preservesComponent (directionComponent l)) ∧
  preservesComponent zComponent ∧
  (∀ epsilon eta : Bool, ∀ M : Finset R2218Direction,
    graphAutomorphismWithInverse (fullGraph epsilon eta M)
      r2218F r2218FInv ∧
      (∀ g x : R2218Group,
        r2218F (r2218RightRegular g (r2218FInv x)) = r2218T g x)) ∧
  Fintype.card FusionParameter = 1024

end
end MathlibPlus.Open.ResearchFormalization.R2218Claims
