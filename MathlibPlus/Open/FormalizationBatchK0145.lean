import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatchK0145

noncomputable section

abbrev Vertex24 := Fin 24

/-- A graph isomorphism between graphs on the fixed 24-vertex carrier. -/
def GraphIso (G H : SimpleGraph Vertex24) : Prop :=
  ∃ e : Equiv.Perm Vertex24,
    ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)

instance graphIsoSetoid : Setoid (SimpleGraph Vertex24) where
  r := GraphIso
  iseqv := by
    constructor
    · intro G
      exact ⟨Equiv.refl _, by simp⟩
    · intro G H ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      intro v w
      obtain ⟨v', rfl⟩ := e.surjective v
      obtain ⟨w', rfl⟩ := e.surjective w
      simpa using (he v' w').symm
    · intro G H K ⟨e, he⟩ ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      intro v w
      simpa [Equiv.trans_apply] using (he v w).trans (hf (e v) (e w))

abbrev GraphClass24 := Quotient graphIsoSetoid

noncomputable instance graphClass24Fintype : Fintype GraphClass24 := Fintype.ofFinite _

def IsR45 (G : SimpleGraph Vertex24) : Prop :=
  (∀ f : Fin 4 ↪ Vertex24,
      ∃ i j, i ≠ j ∧ ¬G.Adj (f i) (f j)) ∧
  (∀ f : Fin 5 ↪ Vertex24,
      ∃ i j, i ≠ j ∧ G.Adj (f i) (f j))

def GraphAut (G : SimpleGraph Vertex24) :=
  {p : Equiv.Perm Vertex24 // ∀ v w, G.Adj (p v) (p w) ↔ G.Adj v w}

instance graphAutFinite (G : SimpleGraph Vertex24) : Finite (GraphAut G) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance graphAutFintype (G : SimpleGraph Vertex24) : Fintype (GraphAut G) :=
  Fintype.ofFinite _

def ClassHasR45 (c : GraphClass24) : Prop :=
  ∃ G : SimpleGraph Vertex24, Quotient.mk' G = c ∧ IsR45 G

def ClassHasAutCard (c : GraphClass24) (n : Nat) : Prop :=
  ∃ G : SimpleGraph Vertex24,
    Quotient.mk' G = c ∧ IsR45 G ∧ Fintype.card (GraphAut G) = n

def ClassHasNontrivialAut (c : GraphClass24) : Prop :=
  ∃ G : SimpleGraph Vertex24,
    Quotient.mk' G = c ∧ IsR45 G ∧ Fintype.card (GraphAut G) ≠ 1

instance classHasAutCardFinite (n : Nat) :
    Finite {c : GraphClass24 // ClassHasAutCard c n} :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance classHasAutCardFintype (n : Nat) :
    Fintype {c : GraphClass24 // ClassHasAutCard c n} := Fintype.ofFinite _

instance classHasNontrivialAutFinite :
    Finite {c : GraphClass24 // ClassHasNontrivialAut c} :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance classHasNontrivialAutFintype :
    Fintype {c : GraphClass24 // ClassHasNontrivialAut c} := Fintype.ofFinite _

instance classHasR45Finite :
    Finite {c : GraphClass24 // ClassHasR45 c} :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance classHasR45Fintype :
    Fintype {c : GraphClass24 // ClassHasR45 c} := Fintype.ofFinite _

noncomputable def AsymmetricCatalogueCount : Nat :=
  Fintype.card {c : GraphClass24 // ClassHasAutCard c 1}

noncomputable def NontrivialAutomorphismCatalogueCount : Nat :=
  Fintype.card {c : GraphClass24 // ClassHasNontrivialAut c}

/-- Exact asymmetric/nontrivial automorphism totals for the 24-vertex `R(4,5)` catalogue. -/
def claim9143 : Prop :=
  AsymmetricCatalogueCount = 341171 ∧
  NontrivialAutomorphismCatalogueCount = 11195 ∧
  AsymmetricCatalogueCount + NontrivialAutomorphismCatalogueCount = 352366

end

end MathlibPlus.Open.FormalizationBatchK0145
