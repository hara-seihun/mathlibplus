import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.Claim35418HistogramNeutralReroot

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Vertex := Fin 6

def c : Vertex := 0
def a : Vertex := 1
def b : Vertex := 2
def u : Vertex := 3
def w : Vertex := 4
def z : Vertex := 5

/-- A rooted presentation records the actual parent map, root, and a rank
certificate carrier; the tree axioms are stated separately below. -/
structure RootedPresentation where
  parent : Vertex → Option Vertex
  root : Vertex
  rank : Vertex → ℕ

def parentAtC (v : Vertex) : Option Vertex :=
  if v = c then none else
    if v = a then some c else
      if v = b then some c else
        if v = u then some c else
          if v = w then some u else some w

def parentAtU (v : Vertex) : Option Vertex :=
  if v = u then none else
    if v = c then some u else
      if v = a then some c else
        if v = b then some c else
          if v = w then some u else some w

def rankAtC (v : Vertex) : ℕ :=
  if v = c then 0 else
    if v = a then 1 else
      if v = b then 1 else
        if v = u then 1 else
          if v = w then 2 else 3

def rankAtU (v : Vertex) : ℕ :=
  if v = u then 0 else
    if v = c then 1 else
      if v = w then 1 else 2

def rootedAtC : RootedPresentation :=
  { parent := parentAtC, root := c, rank := rankAtC }

def rootedAtU : RootedPresentation :=
  { parent := parentAtU, root := u, rank := rankAtU }

def adjacency (P : RootedPresentation) (x y : Vertex) : Prop :=
  P.parent x = some y ∨ P.parent y = some x

/-- The six-vertex host edge set `ca, cb, cu, uw, wz`, with both
orientations displayed because it is used as an adjacency relation. -/
def hostEdge (x y : Vertex) : Prop :=
  (x = c ∧ y = a) ∨ (x = a ∧ y = c) ∨
    (x = c ∧ y = b) ∨ (x = b ∧ y = c) ∨
      (x = c ∧ y = u) ∨ (x = u ∧ y = c) ∨
        (x = u ∧ y = w) ∨ (x = w ∧ y = u) ∨
          (x = w ∧ y = z) ∨ (x = z ∧ y = w)

def rootedTreePresentation (P : RootedPresentation) : Prop :=
  P.parent P.root = none ∧
    (∀ v : Vertex, v ≠ P.root → ∃ p : Vertex, P.parent v = some p) ∧
      (∀ v p : Vertex, P.parent v = some p → P.rank p < P.rank v)

def descendant (P : RootedPresentation) (v x : Vertex) : Prop :=
  Relation.ReflTransGen (fun p q : Vertex => P.parent q = some p) v x

def fringe (P : RootedPresentation) (v : Vertex) : Finset Vertex :=
  (Finset.univ : Finset Vertex).filter (descendant P v)

def fringeOrder (P : RootedPresentation) (v : Vertex) : ℕ :=
  (fringe P v).card

def fringeRootDegree (P : RootedPresentation) (v : Vertex) : ℕ :=
  ((Finset.univ : Finset Vertex).filter
    (fun x => x ∈ fringe P v ∧ P.parent x = some v)).card

/-- Rooted-fringe isomorphism is defined on the actual descendant sets and
preserves the actual parent relation inside those sets. -/
def rootedFringeIsomorphic
    (P Q : RootedPresentation) (v w : Vertex) : Prop :=
  ∃ e : Vertex → Vertex,
    Set.BijOn e (fringe P v : Set Vertex) (fringe Q w : Set Vertex) ∧
      e v = w ∧
        ∀ x y : Vertex,
          x ∈ fringe P v → y ∈ fringe P v →
            (P.parent x = some y ↔ Q.parent (e x) = some (e y))

def rootedPresentationIsomorphic
    (P Q : RootedPresentation) : Prop :=
  ∃ e : Equiv.Perm Vertex,
    e P.root = Q.root ∧
      ∀ x y : Vertex,
        adjacency P x y ↔ adjacency Q (e x) (e y)

/-- Equality of the complete proper occurrence inventories is a permutation of
all nonroot occurrence vertices, preserving both their orders and their actual
rooted-fringe types. -/
def typedOccurrenceInventoryEqual
    (P Q : RootedPresentation) : Prop :=
  ∃ π : Equiv.Perm Vertex,
    ∀ v : Vertex, v ≠ P.root →
      π v ≠ Q.root ∧
        fringeOrder P v = fringeOrder Q (π v) ∧
          rootedFringeIsomorphic P Q v (π v)

def completeDescendantOrderHistogram
    (P : RootedPresentation) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset Vertex).filter
    (fun v => fringeOrder P v = k)).card

def completeHistogramValue (k : ℕ) : ℕ :=
  if k = 1 then 3 else
    if k = 2 then 1 else
      if k = 3 then 1 else
        if k = 6 then 1 else 0

def orderMoment (P : RootedPresentation) (j : ℕ) : ℕ :=
  ∑ v : Vertex, fringeOrder P v ^ j

/-- Claim 35418: the actual six-vertex tree has identical complete
order histograms under roots `c` and `u`, but its proper rooted-fringe
occurrence inventories differ; the order-three occurrences are the actual
path and fork fringes. -/
def claim35418 : Prop :=
  let P := rootedAtC
  let Q := rootedAtU
  rootedTreePresentation P ∧
    rootedTreePresentation Q ∧
      (∀ x y : Vertex, adjacency P x y ↔ hostEdge x y) ∧
        (∀ x y : Vertex, adjacency Q x y ↔ hostEdge x y) ∧
          P.root = c ∧ Q.root = u ∧
            ¬ rootedPresentationIsomorphic P Q ∧
              (∀ k : ℕ,
                completeDescendantOrderHistogram P k =
                    completeHistogramValue k ∧
                  completeDescendantOrderHistogram Q k =
                    completeHistogramValue k) ∧
                (∀ k : ℕ,
                  completeDescendantOrderHistogram P k =
                    completeDescendantOrderHistogram Q k) ∧
                  (∀ j : ℕ, orderMoment P j = orderMoment Q j) ∧
                    completeDescendantOrderHistogram P 1 = 3 ∧
                      completeDescendantOrderHistogram P 2 = 1 ∧
                        completeDescendantOrderHistogram P 3 = 1 ∧
                          completeDescendantOrderHistogram P 6 = 1 ∧
                            fringeOrder P u = 3 ∧
                              fringeRootDegree P u = 1 ∧
                                fringeOrder Q c = 3 ∧
                                  fringeRootDegree Q c = 2 ∧
                                    ¬ rootedFringeIsomorphic P Q u c ∧
                                      ¬ typedOccurrenceInventoryEqual P Q

end

end MathlibPlus.Open.ResearchFormalization.Claim35418HistogramNeutralReroot
