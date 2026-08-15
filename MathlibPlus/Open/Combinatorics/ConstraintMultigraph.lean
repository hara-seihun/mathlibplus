import Mathlib

namespace MathlibPlus.Open.Combinatorics

abbrev TwoSubset (V : Type*) [DecidableEq V] := {e : Finset V // e.card = 2}

abbrev ConstraintVertex (V : Type*) [DecidableEq V] :=
  TwoSubset V ⊕ TwoSubset V

abbrev ConstraintEdge (V : Type*) [DecidableEq V] :=
  {c : V × TwoSubset V // c.1 ∉ c.2.1}

def permuteTwoSubset {V : Type*} [DecidableEq V]
    (σ : Equiv.Perm V) (e : TwoSubset V) : TwoSubset V :=
  ⟨e.1.map σ.toEmbedding, by simpa using e.2⟩

def permuteAvoidingTwoSubset {V : Type*} [DecidableEq V]
    (i : V) (σ : Equiv.Perm V) (hfix : σ i = i)
    (e : {e : TwoSubset V // i ∉ e.1}) :
    {e : TwoSubset V // i ∉ e.1} :=
  ⟨permuteTwoSubset σ e.1, by
    intro hi
    rcases Finset.mem_map.1 hi with ⟨x, hx, hxi⟩
    have hxx : x = i := σ.injective (hxi.trans hfix.symm)
    exact e.2 (hxx ▸ hx)⟩

def IsPrescribedPointedLocalPermutations
    (V : Type*) [Fintype V] [DecidableEq V]
    (n : ℕ) (π : V → Equiv.Perm V) : Prop :=
  Fintype.card V = n ∧
    ∀ i : V,
      π i i = i ∧
        ∀ hfix : π i i = i,
          Function.Bijective (permuteAvoidingTwoSubset i (π i) hfix)

def constraintLeft {V : Type*} [DecidableEq V]
    (c : ConstraintEdge V) : ConstraintVertex V :=
  Sum.inl c.1.2

def constraintRight {V : Type*} [DecidableEq V]
    (π : V → Equiv.Perm V) (c : ConstraintEdge V) : ConstraintVertex V :=
  Sum.inr (permuteTwoSubset (π c.1.1) c.1.2)

def constraintAdjacent {V : Type*} [DecidableEq V]
    (π : V → Equiv.Perm V) (x y : ConstraintVertex V) : Prop :=
  ∃ c : ConstraintEdge V,
    (constraintLeft c = x ∧ constraintRight π c = y) ∨
      (constraintLeft c = y ∧ constraintRight π c = x)

def constraintComponent {V : Type*} [DecidableEq V]
    (π : V → Equiv.Perm V) (C : Set (ConstraintVertex V)) : Prop :=
  ∃ v : ConstraintVertex V,
    C = {w | Relation.ReflTransGen (constraintAdjacent π) v w}

def constraintIncidentEdges {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V) (v : ConstraintVertex V) : Finset (ConstraintEdge V) :=
  Finset.univ.filter (fun c => constraintLeft c = v ∨ constraintRight π c = v)

def constraintDegree {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → Equiv.Perm V) (v : ConstraintVertex V) : ℕ :=
  (constraintIncidentEdges π v).card

def constraintBipartite {V : Type*} [DecidableEq V]
    (π : V → Equiv.Perm V) : Prop :=
  ∀ c : ConstraintEdge V,
    ∃ eL eR : TwoSubset V,
      constraintLeft c = Sum.inl eL ∧
        constraintRight π c = Sum.inr eR

def constraintMultigraphRegularity : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (n : ℕ) (π : V → Equiv.Perm V),
    IsPrescribedPointedLocalPermutations V n π →
      constraintBipartite π ∧
        ∀ v : ConstraintVertex V, constraintDegree π v = n - 2

noncomputable def constraintLeftCount {V : Type*} [Fintype V] [DecidableEq V]
    (C : Set (ConstraintVertex V)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : TwoSubset V => Sum.inl e ∈ C)).card

noncomputable def constraintRightCount {V : Type*} [Fintype V] [DecidableEq V]
    (C : Set (ConstraintVertex V)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : TwoSubset V => Sum.inr e ∈ C)).card

def constraintComponentLeftRightBalance : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (n : ℕ) (π : V → Equiv.Perm V),
    IsPrescribedPointedLocalPermutations V n π →
      n ≥ 3 →
        ∀ C : Set (ConstraintVertex V),
          constraintComponent π C →
            constraintLeftCount C = constraintRightCount C

end MathlibPlus.Open.Combinatorics
