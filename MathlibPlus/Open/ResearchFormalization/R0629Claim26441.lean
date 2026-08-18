import MathlibPlus.Open.Graphs.BasisTranspose

namespace MathlibPlus.Open.ResearchFormalization.R0629Claim26441

noncomputable section

open Classical
open MathlibPlus.Open.Graphs
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A connected regular vertex-transitive graph on ten vertices, with its
specified degree. -/
def connectedRegularVertexTransitive
    (G : SimpleGraph (Fin 10)) (d : ℕ) : Prop :=
  (∀ v : Fin 10,
    (Finset.univ.filter (fun w : Fin 10 => G.Adj v w)).card = d) ∧
    G.Connected ∧
      (∀ v w : Fin 10, ∃ e : G ≃g G, e v = w)

/-- The retained order-ten host classes are generated in degrees two through
four and then closed under graph complementation. -/
def retainedHostClass (H : GraphIsoClass 10) : Prop :=
  ∃ d : ℕ, 2 ≤ d ∧ d ≤ 4 ∧
    (connectedRegularVertexTransitive (graphRepresentative H) d ∨
      connectedRegularVertexTransitive (graphRepresentative H)ᶜ d)

noncomputable def retainedHostClasses : Finset (GraphIsoClass 10) :=
  Finset.univ.filter retainedHostClass

def retainedExtensionColumn (G : GraphIsoClass 11) : Prop :=
  ∃ H : GraphIsoClass 10,
    retainedHostClass H ∧ 0 < deletionMultiplicity G H

noncomputable def retainedColumns : Finset (GraphIsoClass 11) :=
  Finset.univ.filter retainedExtensionColumn

/-- A cubic feature is a multiset of three canonical vertex-card types that
is drawable without replacement from the graph's deck profile. -/
def cubicCardFeature (G : GraphIsoClass 11)
    (f : Multiset (GraphIsoClass 10)) : Prop :=
  f.card = 3 ∧
    ∀ H : GraphIsoClass 10,
      f.count H ≤ deletionMultiplicity G H

def remainingColumns (C : Finset (GraphIsoClass 11))
    (order : Fin 2640 → GraphIsoClass 11) (i : Fin 2640) :
    Finset (GraphIsoClass 11) :=
  C.filter (fun G => ∀ j : Fin 2640, j.val < i.val → G ≠ order j)

/-- A complete singleton peel is the exact three-card stopping operation: at
step i the displayed cubic pivot has precisely the selected current column in
its support. -/
def completeSingletonPeel (C : Finset (GraphIsoClass 11)) : Prop :=
  ∃ order : Fin 2640 → GraphIsoClass 11,
    (∀ i j : Fin 2640, order i = order j → i = j) ∧
      (∀ G : GraphIsoClass 11,
        G ∈ C ↔ ∃ i : Fin 2640, order i = G) ∧
      ∃ pivot : Fin 2640 → Multiset (GraphIsoClass 10),
        ∀ i : Fin 2640,
          (remainingColumns C order i).filter
              (fun G => cubicCardFeature G (pivot i)) = {order i}

/-- Claim 26441: the complete cubic support matrix on the exact retained
2,640-column block has an empty three-card stopping core. -/
def claim26441 : Prop :=
  retainedHostClasses.card = 14 ∧
    retainedColumns.card = 2640 ∧
    (∀ G : GraphIsoClass 11,
      G ∈ retainedColumns ↔
        graphClass (graphRepresentative G)ᶜ ∈ retainedColumns) ∧
    completeSingletonPeel retainedColumns

end

end MathlibPlus.Open.ResearchFormalization.R0629Claim26441
