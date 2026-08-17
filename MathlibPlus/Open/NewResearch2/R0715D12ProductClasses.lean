import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0715D12ProductClasses

open SimpleGraph

noncomputable section

/-- The dihedral group of order twelve in Mathlib's `Dih(C₆)` model. -/
abbrev D12 := DihedralGroup 6

/-- The three exact inverse-closed connection sets from the admitted packet. -/
def connectionSet0 : Set D12 :=
  {DihedralGroup.r 1, DihedralGroup.r 3, DihedralGroup.r 5,
    DihedralGroup.sr 0}

def connectionSet1 : Set D12 :=
  {DihedralGroup.r 3, DihedralGroup.sr 0,
    DihedralGroup.sr 2, DihedralGroup.sr 4}

def connectionSet2 : Set D12 :=
  {DihedralGroup.sr 0, DihedralGroup.sr 5,
    DihedralGroup.sr 2, DihedralGroup.sr 4}

/-- The exact three-set indexing used by the D₁₂ fiber. -/
def connectionSet (i : Fin 3) : Set D12 :=
  match i.1 with
  | 0 => connectionSet0
  | 1 => connectionSet1
  | _ => connectionSet2

/-- The ordinary undirected Cayley graph for one of the displayed sets. -/
def cayleyGraph (i : Fin 3) : SimpleGraph D12 :=
  SimpleGraph.mulCayley (connectionSet i)

/-- Twin-freeness as distinct open neighborhoods. -/
def twinFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ x y : V, x ≠ y → G.neighborSet x ≠ G.neighborSet y

/-- The common product graph `K_{3,3} □ K₂`. -/
def commonGraph : SimpleGraph ((Fin 3 ⊕ Fin 3) × Fin 2) :=
  (completeBipartiteGraph (Fin 3) (Fin 3)) □
    SimpleGraph.completeGraph (Fin 2)

/-- Claim 24193: all three exact D₁₂ Cayley graphs are connected, twin-free,
and isomorphic to the same `K_{3,3} □ K₂` graph. -/
def claim24193 : Prop :=
  ∀ i : Fin 3,
    (cayleyGraph i).Connected ∧
      twinFree (cayleyGraph i) ∧
      Nonempty (cayleyGraph i ≃g commonGraph)

/-- The rotation subgroup of D₁₂ in the presentation `r^k`. -/
def rotationSet : Set D12 :=
  Set.range (DihedralGroup.r : ZMod 6 → D12)

/-- The number of rotations in a connection set. -/
def rotationCount (S : Set D12) : ℕ :=
  Set.ncard (S ∩ rotationSet)

/-- Claim 24194: the exact rotation counts are `3,1,0`; every group
automorphism preserves the rotation subgroup; and the three sets are in
distinct automorphism orbits. -/
def claim24194 : Prop :=
  (rotationCount connectionSet0 = 3 ∧
    rotationCount connectionSet1 = 1 ∧
    rotationCount connectionSet2 = 0) ∧
  (∀ φ : D12 ≃* D12, φ '' rotationSet = rotationSet) ∧
  (∀ i j : Fin 3, i ≠ j →
    ¬ ∃ φ : D12 ≃* D12,
      Set.image φ (connectionSet i) = connectionSet j)

/-- The two copies of `S₃` in product coordinates. -/
abbrev S3 := Equiv.Perm (Fin 3)

/-- A raw carrier for `((S₃×S₃)⋊C₂)×C₂`, with both C₂ bits explicit. -/
abbrev AutModel := ((S3 × S3) × Bool) × Bool

/-- The semidirect-product multiplication in product coordinates. -/
def modelMul (x y : AutModel) : AutModel :=
  let acted : S3 × S3 :=
    if x.1.2 then (y.1.1.2, y.1.1.1) else y.1.1
  ((x.1.1 * acted, Bool.xor x.1.2 y.1.2),
    Bool.xor x.2 y.2)

/-- The identity in the displayed product-coordinate model. -/
def modelOne : AutModel :=
  ((1, 1), false) |> fun p => (p, false)

/-- The last `C₂` factor, whose action is the layer flip. -/
def modelLayerFlip : AutModel :=
  ((1, 1), false) |> fun p => (p, true)

/-- The graph automorphism carrier of a simple graph, retaining the actual
adjacency-preservation predicate rather than an unrelated permutation type. -/
def graphAutCarrier {V : Type*} (G : SimpleGraph V) :=
  {e : Equiv.Perm V // ∀ x y : V,
    G.Adj (e x) (e y) ↔ G.Adj x y}

/-- Multiplication in the graph-automorphism carrier, stated on its actual
permutation representatives. -/
def graphAutProduct {V : Type*} (G : SimpleGraph V)
    (f g h : graphAutCarrier G) : Prop :=
  h.1 = f.1 * g.1

/-- The layer-flipping permutation of the common product graph. -/
def layerFlipVertexEquiv :
    Equiv.Perm ((Fin 3 ⊕ Fin 3) × Fin 2) :=
  Equiv.prodCongr (Equiv.refl (Fin 3 ⊕ Fin 3))
    (Equiv.swap (0 : Fin 2) (1 : Fin 2))

/-- The exact raw relation expressing the graph automorphism group as the
specified semidirect/direct-product group.  Product preservation is written
against actual composition on graph automorphisms, while the target operation
is the displayed semidirect multiplication. -/
def graphAutModelIsomorphism : Prop :=
  ∃ e : graphAutCarrier commonGraph ≃ AutModel,
    (∀ f g : graphAutCarrier commonGraph,
      ∃ h : graphAutCarrier commonGraph, graphAutProduct commonGraph f g h) ∧
    (∀ f g h : graphAutCarrier commonGraph,
      graphAutProduct commonGraph f g h →
        e h = modelMul (e f) (e g)) ∧
    (∃ f : graphAutCarrier commonGraph,
      f.1 = 1 ∧ e f = modelOne) ∧
    (∀ x y z : AutModel,
      modelMul (modelMul x y) z = modelMul x (modelMul y z)) ∧
    (∀ x : AutModel,
      modelMul modelOne x = x ∧ modelMul x modelOne = x) ∧
    (∀ x : AutModel, ∃ y : AutModel,
      modelMul x y = modelOne ∧ modelMul y x = modelOne) ∧
    (∃ f : graphAutCarrier commonGraph,
      f.1 = layerFlipVertexEquiv ∧ e f = modelLayerFlip)

/-- Claim 24195: the common graph has the displayed automorphism-group model,
its order is 144, and the final C₂ is the actual two-layer flip. -/
def claim24195 : Prop :=
  graphAutModelIsomorphism ∧
    Nat.card AutModel = 144

end

end MathlibPlus.Open.NewResearch2.R0715D12ProductClasses
