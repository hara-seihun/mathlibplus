import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-! The two explicit four-vertex graphs in admitted claim 47254. -/

abbrev Graph4 := Fin 4 → Fin 4 → ℕ

 def p3DisjointSingleton : Graph4 := fun i j =>
  if ((i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
      (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1)) then 1 else 0

 def twoDisjointEdges : Graph4 := fun i j =>
  if ((i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
      (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2)) then 1 else 0

 def IsSimpleGraph4 (g : Graph4) : Prop :=
  (∀ i, g i i = 0) ∧
  (∀ i j, g i j = g j i) ∧
  (∀ i j, g i j ≤ 1)

 def edgeCount (g : Graph4) : ℕ :=
  (Finset.univ.filter (fun p : Fin 4 × Fin 4 =>
    p.1.val < p.2.val ∧ g p.1 p.2 = 1)).card

 def Graph4Isomorphic (g h : Graph4) : Prop :=
  ∃ e : Equiv.Perm (Fin 4), ∀ i j, g (e i) (e j) = h i j

abbrev OrderedTriple := Fin 3 → Fin 4

def orderedTriple (t : OrderedTriple) : Prop :=
  t 0 ≠ t 1 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2

instance (t : OrderedTriple) : Decidable (orderedTriple t) := by
  unfold orderedTriple
  infer_instance

def orderedTriples : Finset OrderedTriple :=
  Finset.univ.filter orderedTriple

def pairLeft (k : Fin 3) : Fin 3 :=
  if k.val = 2 then 1 else 0

def pairRight (k : Fin 3) : Fin 3 :=
  if k.val = 0 then 1 else 2

def commonNeighbours (g : Graph4) (i j : Fin 4) : ℕ :=
  ∑ z : Fin 4, if g i z = 1 ∧ g j z = 1 then 1 else 0

structure GramSignature where
  internalEdges : Fin 3 → ℕ
  hostDegrees : Fin 3 → ℕ
  commonNeighbourCounts : Fin 3 → ℕ
  deriving DecidableEq

def gramSignature (g : Graph4) (t : OrderedTriple) : GramSignature :=
  { internalEdges := fun k => g (t (pairLeft k)) (t (pairRight k))
    hostDegrees := fun k => ∑ j : Fin 4, g (t k) j
    commonNeighbourCounts := fun k =>
      commonNeighbours g (t (pairLeft k)) (t (pairRight k)) }

def gramCensus (g : Graph4) (s : GramSignature) : ℕ :=
  (orderedTriples.filter (fun t => gramSignature g t = s)).card

def gramCoordinates (g h : Graph4) : Finset GramSignature :=
  (orderedTriples.image (gramSignature g)) ∪
    (orderedTriples.image (gramSignature h))

def differingGramCoordinates (g h : Graph4) : ℕ :=
  ((gramCoordinates g h).filter (fun s => gramCensus g s ≠ gramCensus h s)).card

def triple (a b c : ℕ) : Fin 3 → ℕ := fun k =>
  if k.val = 0 then a else if k.val = 1 then b else c

def displayedGramSignature : GramSignature :=
  { internalEdges := triple 0 0 0
    hostDegrees := triple 0 1 1
    commonNeighbourCounts := triple 0 0 1 }

/-- Exact open formalization of admitted claim 47254. -/
def claim47254 : Prop :=
  IsSimpleGraph4 p3DisjointSingleton ∧
  IsSimpleGraph4 twoDisjointEdges ∧
  ¬ Graph4Isomorphic p3DisjointSingleton twoDisjointEdges ∧
  edgeCount p3DisjointSingleton = edgeCount twoDisjointEdges ∧
  gramCensus p3DisjointSingleton displayedGramSignature = 2 ∧
  gramCensus twoDisjointEdges displayedGramSignature = 0 ∧
  differingGramCoordinates p3DisjointSingleton twoDisjointEdges = 15

end MathlibPlus.Open.ResearchFormalization

