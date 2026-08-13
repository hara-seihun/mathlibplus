/-!
Formalization batch for New Research 2 claims 9075--9082.
-/
import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.GraphTheory

/-- Extension of a graph by one distinguished vertex, with attachment set `X`. -/
def oneVertexExtension {W : Type*} (C : SimpleGraph W) (X : Set W) :
    SimpleGraph (Option W) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | none, none => False
    | none, some w => w ∈ X
    | some w, none => w ∈ X
    | some w, some z => C.Adj w z)

def graphDegree {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  letI := Fintype.ofFinite {w : V // G.Adj v w}
  exact Fintype.card {w : V // G.Adj v w}

def degreeHistogram {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : ℕ := by
  classical
  letI := Fintype.ofFinite {v : V // graphDegree G v = d}
  exact Fintype.card {v : V // graphDegree G v = d}

def cardDegreeCount {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) (d : ℕ) : ℕ := by
  classical
  letI := Fintype.ofFinite
    {u : {x : V // x ∈ ({v}ᶜ : Set V)} //
      graphDegree (G.induce ({v}ᶜ : Set V)) u = d}
  exact Fintype.card
    {u : {x : V // x ∈ ({v}ᶜ : Set V)} //
      graphDegree (G.induce ({v}ᶜ : Set V)) u = d}

def attachmentDegreeCount {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    (d : ℕ) : ℕ := by
  classical
  letI := Fintype.ofFinite
    {u : {x : V // x ∈ ({v}ᶜ : Set V)} //
      G.Adj u.1 v ∧ graphDegree (G.induce ({v}ᶜ : Set V)) u = d}
  exact Fintype.card
    {u : {x : V // x ∈ ({v}ᶜ : Set V)} //
      G.Adj u.1 v ∧ graphDegree (G.induce ({v}ᶜ : Set V)) u = d}

def previousAttachmentDegreeCount {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)
    (d : ℕ) : ℤ :=
  if d = 0 then 0 else attachmentDegreeCount G v (d - 1)

def deckDegreeCount {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : ℕ :=
  ∑ v : V, cardDegreeCount G v d

def inducedCopyCount {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph W) (G : SimpleGraph V) : ℕ := by
  classical
  letI := Fintype.ofFinite
    {S : Finset V //
      S.card = Fintype.card W ∧
        Nonempty (SimpleGraph.Iso F (G.induce (S : Set V)))}
  exact Fintype.card
    {S : Finset V //
      S.card = Fintype.card W ∧
        Nonempty (SimpleGraph.Iso F (G.induce (S : Set V)))}

def rootedInducedCopyCount {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph W) (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  letI := Fintype.ofFinite
    {S : Finset V //
      v ∈ S ∧ S.card = Fintype.card W ∧
        Nonempty (SimpleGraph.Iso F (G.induce (S : Set V)))}
  exact Fintype.card
    {S : Finset V //
      v ∈ S ∧ S.card = Fintype.card W ∧
        Nonempty (SimpleGraph.Iso F (G.induce (S : Set V)))}

def cardFixingExtensionIso {W : Type*} (C : SimpleGraph W) (X Y : Set W) : Prop :=
  ∃ e : SimpleGraph.Iso (oneVertexExtension C X) (oneVertexExtension C Y),
    e none = none

def automorphismAttachmentOrbit {W : Type*} (C : SimpleGraph W) (X Y : Set W) : Prop :=
  ∃ e : SimpleGraph.Iso C C, ∀ w : W, (w ∈ X ↔ e w ∈ Y)

/-- Claim 9075. -/
def claim9075 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) (v : V),
    let C := G.induce ({v}ᶜ : Set V)
    let X : Set {x : V // x ∈ ({v}ᶜ : Set V)} := {u | G.Adj u.1 v}
    let k := graphDegree G v
    Nonempty (SimpleGraph.Iso G (oneVertexExtension C X)) ∧
      k = Fintype.card {u : V // G.Adj v u}

/-- Claim 9077. -/
def claim9077 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    3 ≤ Fintype.card V →
      (∑ v : V, (G.induce ({v}ᶜ : Set V)).edgeSet.ncard) =
          (Fintype.card V - 2) * G.edgeSet.ncard ∧
      (∀ d : ℕ,
        deckDegreeCount G d =
          (Fintype.card V - 1 - d) * degreeHistogram G d +
            (d + 1) * degreeHistogram G (d + 1))

/-- Claim 9078. -/
def claim9078 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) (v : V) (d : ℕ),
    (degreeHistogram G d : ℤ) =
      (if graphDegree G v = d then (1 : ℤ) else 0) +
        (cardDegreeCount G v d : ℤ) -
        (attachmentDegreeCount G v d : ℤ) +
        previousAttachmentDegreeCount G v d

/-- Claim 9080. -/
def claim9080 : Prop :=
  ∀ (V W : Type*) [Fintype V] [Fintype W]
    (G : SimpleGraph V) (F : SimpleGraph W),
    Fintype.card W < Fintype.card V →
      (∑ v : V, inducedCopyCount F (G.induce ({v}ᶜ : Set V))) =
        (Fintype.card V - Fintype.card W) * inducedCopyCount F G

/-- Claim 9081. -/
def claim9081 : Prop :=
  ∀ (V W : Type*) [Fintype V] [Fintype W]
    (G : SimpleGraph V) (v : V) (F : SimpleGraph W),
    Fintype.card W < Fintype.card V →
      rootedInducedCopyCount F G v =
        inducedCopyCount F G -
          inducedCopyCount F (G.induce ({v}ᶜ : Set V))

/-- Claim 9082. -/
def claim9082 : Prop :=
  ∀ (W : Type*) (C : SimpleGraph W) (X Y : Set W),
    cardFixingExtensionIso C X Y ↔ automorphismAttachmentOrbit C X Y

end MathlibPlus.Open.GraphTheory
