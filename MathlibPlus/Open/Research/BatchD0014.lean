import Mathlib

namespace MathlibPlus.Open.ResearchBatch.D0014

open scoped BigOperators

/-- An unordered non-diagonal pair of vertices. -/
def SimpleEdge (V : Type*) :=
  {e : Sym2 V // ∃ a b : V, a ≠ b ∧ e = s(a, b)}

/-- The card permutation attached to each deleted vertex, fixing that vertex. -/
def CardCocycle (V : Type*) :=
  ∀ i : V, {σ : Equiv.Perm V // σ i = i}

def avoids (i : V) (e : SimpleEdge V) : Prop :=
  ¬ Sym2.Mem i e.1

def cardMap (c : CardCocycle V) (i : V) : SimpleEdge V → SimpleEdge V :=
  fun e =>
    ⟨Sym2.map (c i).1 e.1, by
      rcases e.2 with ⟨a, b, hab, he⟩
      refine ⟨(c i).1 a, (c i).1 b, (c i).1.injective.ne hab, ?_⟩
      rw [he, Sym2.map_mk]⟩

def constraintStep (c : CardCocycle V)
    (x y : SimpleEdge V ⊕ SimpleEdge V) : Prop :=
  ∃ (i : V) (e : SimpleEdge V), avoids i e ∧
    ((x = Sum.inl e ∧ y = Sum.inr (cardMap c i e)) ∨
      (x = Sum.inr (cardMap c i e) ∧ y = Sum.inl e))

def equalityComponent (c : CardCocycle V)
    (x y : SimpleEdge V ⊕ SimpleEdge V) : Prop :=
  Relation.EqvGen (constraintStep c) x y

def componentColoring (c : CardCocycle V)
    (left right : SimpleEdge V → C) : Prop :=
  ∀ x y, equalityComponent c x y →
    Sum.elim left right x = Sum.elim left right y

def cardCompatible (c : CardCocycle V)
    (left right : SimpleEdge V → C) : Prop :=
  ∀ (i : V) (e : SimpleEdge V), avoids i e →
    left e = right (cardMap c i e)

def compatiblePairsAreExactlyComponentColorings_claim : Prop :=
  ∀ (V : Type*) (c : CardCocycle V) (C : Type*)
    (left right : SimpleEdge V → C),
    componentColoring c left right ↔ cardCompatible c left right

def AdmissibleCardPair (V : Type*) :=
  {p : V × SimpleEdge V // avoids p.1 p.2}

def cardCoboundary (c : CardCocycle V)
    (left right : SimpleEdge V → G) [AddGroup G]
    (p : AdmissibleCardPair V) : G :=
  left p.1.2 - right (cardMap c p.1.1 p.1.2)

def cardCoboundary_claim : Prop :=
  ∀ (V : Type*) (c : CardCocycle V) (G : Type*) [AddGroup G]
    (left right : SimpleEdge V → G) (p : AdmissibleCardPair V),
    cardCoboundary c left right p =
      left p.1.2 - right (cardMap c p.1.1 p.1.2)

noncomputable def constraintMultiplicity [Fintype V]
    (c : CardCocycle V) (e f : SimpleEdge V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => avoids i e ∧ cardMap c i e = f)).card

def closedConstraintComponent (c : CardCocycle V)
    (A B : Finset (SimpleEdge V)) : Prop :=
  (∀ e ∈ A, ∀ i, avoids i e → cardMap c i e ∈ B) ∧
  (∀ f ∈ B, ∀ i, avoids i f →
    ∃ e, e ∈ A ∧ avoids i e ∧ cardMap c i e = f)

noncomputable def regularityOnTheLeft_claim : Prop := by
  classical
  exact ∀ (V : Type*) [Fintype V] (c : CardCocycle V)
    (A B : Finset (SimpleEdge V)),
    closedConstraintComponent c A B →
      ∀ e, e ∈ A →
        (∑ f ∈ B, constraintMultiplicity c e f) = Fintype.card V - 2

end MathlibPlus.Open.ResearchBatch.D0014
