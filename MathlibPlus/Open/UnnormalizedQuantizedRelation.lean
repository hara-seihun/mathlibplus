import Mathlib

namespace MathlibPlus.Open.UnnormalizedQuantizedRelation

open scoped BigOperators

noncomputable section

structure FiniteSimpleGraph (n : ℕ) where
  carrier : Type
  fintype : Fintype carrier
  card_eq : Fintype.card carrier = n
  graph : SimpleGraph carrier

namespace FiniteSimpleGraph

instance (n : ℕ) (G : FiniteSimpleGraph n) : Fintype G.carrier := G.fintype

def Isomorphic {n : ℕ} (G H : FiniteSimpleGraph n) : Prop :=
  Nonempty (G.graph ≃g H.graph)

def setoid (n : ℕ) : Setoid (FiniteSimpleGraph n) where
  r := Isomorphic
  iseqv := by
    constructor
    · intro G
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro G H h
      rcases h with ⟨e⟩
      exact ⟨RelIso.symm e⟩
    · intro G H K h₁ h₂
      rcases h₁ with ⟨e₁⟩
      rcases h₂ with ⟨e₂⟩
      exact ⟨RelIso.trans e₁ e₂⟩

abbrev Class (n : ℕ) := Quotient (setoid n)

abbrev Space (n : ℕ) := Class n →₀ ℚ

def basis {n : ℕ} (G : FiniteSimpleGraph n) : Space n :=
  Finsupp.single (Quotient.mk (setoid n) G) 1

def deleted (G : FiniteSimpleGraph (n + 1)) (v : G.carrier) : FiniteSimpleGraph n := by
  classical
  letI := G.fintype
  exact
    { carrier := {x : G.carrier // x ≠ v}
      fintype := inferInstance
      card_eq := by
        rw [Fintype.card_subtype_compl (fun x : G.carrier => x = v)]
        simp [G.card_eq]
      graph := G.graph.induce {x : G.carrier | x ≠ v} }

abbrev addVertex (G : FiniteSimpleGraph n) (S : Finset G.carrier) :
    FiniteSimpleGraph (n + 1) := by
  classical
  letI := G.fintype
  exact
    { carrier := Option G.carrier
      fintype := inferInstance
      card_eq := by simp [G.card_eq]
      graph := SimpleGraph.fromRel (fun x y =>
        match x, y with
        | some u, some v => G.graph.Adj u v
        | none, some v => v ∈ S
        | some u, none => False
        | none, none => False) }

private def deletedIso {n : ℕ} {G H : FiniteSimpleGraph (n + 1)}
    (e : G.graph ≃g H.graph) (v : G.carrier) :
    (deleted G v).graph ≃g (deleted H (e v)).graph := by
  let q : {x : G.carrier // x ≠ v} ≃ {y : H.carrier // y ≠ e v} :=
    Equiv.subtypeEquiv e.toEquiv (by
      intro x
      constructor
      · intro hx hxe
        exact hx (e.injective hxe)
      · intro hxe hx
        exact hxe (congrArg e hx))
  exact RelIso.mk q (by
    intro x y
    exact e.map_rel_iff)

private def addVertexIso {n : ℕ} {G H : FiniteSimpleGraph n}
    (e : G.graph ≃g H.graph) (S : Finset G.carrier) :
    (addVertex G S).graph ≃g
      (addVertex H (Finset.map e.toEquiv.toEmbedding S)).graph := by
  let q : Option G.carrier ≃ Option H.carrier :=
    { toFun := fun x => match x with | none => none | some u => some (e u)
      invFun := fun x => match x with | none => none | some u => some (e.symm u)
      left_inv := by intro x; cases x <;> simp
      right_inv := by intro x; cases x <;> simp }
  have q_none : q none = none := rfl
  have q_some (u : G.carrier) : q (some u) = some (e u) := rfl
  exact RelIso.mk q (by
    intro x y
    cases x with
    | none =>
        cases y with
        | none =>
            simp [q, addVertex, SimpleGraph.fromRel]
        | some v =>
            simp [q, addVertex, SimpleGraph.fromRel, Finset.mem_map]
            have h : e.symm (e v) = v := e.left_inv v
            exact Iff.of_eq (congrArg (fun x => x ∈ S) h)
    | some u =>
        cases y with
        | none =>
            simp [q, addVertex, SimpleGraph.fromRel]
            have h : e.symm (e u) = u := e.left_inv u
            exact Iff.of_eq (congrArg (fun x => x ∈ S) h)
        | some v =>
            simp [q, addVertex, SimpleGraph.fromRel, Finset.mem_map, e.map_rel_iff]
  )

private def deckBasis (G : FiniteSimpleGraph (n + 1)) : Space n := by
  letI := G.fintype
  exact ∑ v : G.carrier, basis (deleted G v)

private def genericLiftBasis (G : FiniteSimpleGraph n) : Space (n + 1) := by
  letI := G.fintype
  exact ∑ S : Finset G.carrier, basis (addVertex G S)

private def deckBasis_respects_iso {n : ℕ} {G H : FiniteSimpleGraph (n + 1)}
    (e : G.graph ≃g H.graph) : deckBasis G = deckBasis H := by
  letI := G.fintype
  letI := H.fintype
  apply Fintype.sum_equiv e.toEquiv
  intro v
  change Finsupp.single (Quotient.mk (setoid n) (deleted G v)) 1 =
    Finsupp.single (Quotient.mk (setoid n) (deleted H (e v))) 1
  apply congrArg (fun X : Class n => Finsupp.single X 1)
  exact Quotient.sound (s := setoid n) (a := deleted G v)
    (b := deleted H (e v)) ⟨deletedIso e v⟩

private def genericLiftBasis_respects_iso {n : ℕ} {G H : FiniteSimpleGraph n}
    (e : G.graph ≃g H.graph) : genericLiftBasis G = genericLiftBasis H := by
  letI := G.fintype
  letI := H.fintype
  apply Fintype.sum_equiv (Equiv.finsetCongr e.toEquiv)
  intro S
  change Finsupp.single (Quotient.mk (setoid (n + 1)) (addVertex G S)) 1 =
    Finsupp.single (Quotient.mk (setoid (n + 1))
      (addVertex H (Finset.map e.toEquiv.toEmbedding S))) 1
  apply congrArg (fun X : Class (n + 1) => Finsupp.single X 1)
  exact Quotient.sound (s := setoid (n + 1)) (a := addVertex G S)
    (b := addVertex H (Finset.map e.toEquiv.toEmbedding S)) ⟨addVertexIso e S⟩

def deck : Space (n + 1) →ₗ[ℚ] Space n := by
  let f : FiniteSimpleGraph (n + 1) → Space n := deckBasis
  let hf : ∀ G H : FiniteSimpleGraph (n + 1), Isomorphic G H → f G = f H := by
    intro G H h
    rcases h with ⟨e⟩
    exact deckBasis_respects_iso e
  let q : Class (n + 1) → Space n := Quotient.lift f hf
  exact Finsupp.linearCombination ℚ q

def genericLift : Space n →ₗ[ℚ] Space (n + 1) := by
  let f : FiniteSimpleGraph n → Space (n + 1) := genericLiftBasis
  let hf : ∀ G H : FiniteSimpleGraph n, Isomorphic G H → f G = f H := by
    intro G H h
    rcases h with ⟨e⟩
    exact genericLiftBasis_respects_iso e
  let q : Class n → Space (n + 1) := Quotient.lift f hf
  exact Finsupp.linearCombination ℚ q

end FiniteSimpleGraph

def lower (n : ℕ) : FiniteSimpleGraph.Space n →ₗ[ℚ]
    FiniteSimpleGraph.Space (n - 1) :=
  match n with
  | 0 => 0
  | m + 1 => FiniteSimpleGraph.deck (n := m)

def upperPrevious (n : ℕ) : FiniteSimpleGraph.Space (n - 1) →ₗ[ℚ]
    FiniteSimpleGraph.Space n :=
  match n with
  | 0 => 0
  | m + 1 => FiniteSimpleGraph.genericLift (n := m)

def normalizedLift (n : ℕ) : FiniteSimpleGraph.Space n →ₗ[ℚ]
    FiniteSimpleGraph.Space (n + 1) :=
  ((2 : ℚ) ^ n)⁻¹ • FiniteSimpleGraph.genericLift (n := n)

def normalizedUpperPrevious (n : ℕ) :
    FiniteSimpleGraph.Space (n - 1) →ₗ[ℚ] FiniteSimpleGraph.Space n :=
  match n with
  | 0 => 0
  | m + 1 => ((2 : ℚ) ^ m)⁻¹ • FiniteSimpleGraph.genericLift (n := m)

/-- Claim 5006: the unnormalized generic lift has the degree-dependent relation,
while the scalar normalization needed for the deck-depth theory is `2⁻ⁿ`. -/
def claim5006 : Prop :=
  (∀ n : ℕ,
    FiniteSimpleGraph.deck (n := n) ∘ₗ FiniteSimpleGraph.genericLift (n := n) =
      (2 : ℚ) ^ n • LinearMap.id +
        (2 : ℚ) • (upperPrevious n ∘ₗ lower n)) ∧
  (∀ n : ℕ,
    FiniteSimpleGraph.deck (n := n) ∘ₗ normalizedLift n -
        (normalizedUpperPrevious n ∘ₗ lower n) =
      LinearMap.id) ∧
  ¬ (∃ c : ℚ, ∀ n : ℕ,
    FiniteSimpleGraph.deck (n := n) ∘ₗ FiniteSimpleGraph.genericLift (n := n) -
        (upperPrevious n ∘ₗ lower n) =
      c • LinearMap.id)

end

end MathlibPlus.Open.UnnormalizedQuantizedRelation
