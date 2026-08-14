import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics

noncomputable section

/-- Labelled representatives for the unlabelled finite `n`-vertex tree state space. -/
def TreeGraph (n : ℕ) :=
  {G : SimpleGraph (Fin n) // G.IsTree}

def treeGraphSetoid (n : ℕ) : Setoid (TreeGraph n) where
  r A B := Nonempty (A.1 ≃g B.1)
  iseqv := {
    refl := fun A => ⟨SimpleGraph.Iso.refl⟩
    symm := fun h => by
      rcases h with ⟨f⟩
      exact ⟨f.symm⟩
    trans := fun h₁ h₂ => by
      rcases h₁ with ⟨f⟩
      rcases h₂ with ⟨g⟩
      exact ⟨SimpleGraph.Iso.comp g f⟩ }

/-- `T_n`, the type of unlabelled `n`-vertex trees. -/
def TreeState (n : ℕ) := Quotient (treeGraphSetoid n)

abbrev TreeVector (n : ℕ) := TreeState n →₀ ℚ

/-- The graph isomorphism induced by pulling a graph back along an equivalence. -/
def comapIso {α β : Type*} (e : α ≃ β) (G : SimpleGraph β) :
    SimpleGraph.comap e G ≃g G :=
  RelIso.mk e (by
    intro a b
    simp [SimpleGraph.comap_adj])

/-- The card obtained by deleting a specified leaf from a representative on `m+2` vertices. -/
def leafCardGraph (m : ℕ) (G : TreeGraph (m + 2)) (ℓ : Fin (m + 2))
    [Fintype {v // v ∈ G.1.neighborSet ℓ}] (hℓ : G.1.degree ℓ = 1) : TreeGraph (m + 1) := by
  have hG : G.1.IsTree := G.2
  have htree : (G.1.induce (Set.compl (Set.singleton ℓ))).IsTree :=
    ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hℓ,
      hG.isAcyclic.induce _⟩
  let e₀ : Fin (m + 1) ≃ ({ℓ}ᶜ : Finset (Fin (m + 2))) :=
    (Fin.succAboveOrderIso ℓ).toEquiv
  let e : Fin (m + 1) ≃ {v : Fin (m + 2) // v ∈ Set.compl (Set.singleton ℓ)} :=
    { toFun := fun i => ⟨e₀ i, by
        change (e₀ i : Fin (m + 2)) ≠ ℓ
        exact Fin.succAbove_ne ℓ i⟩
      invFun := fun v => e₀.symm ⟨v.1, by
        apply Finset.mem_compl.mpr
        intro hv
        exact v.2 (Set.mem_singleton_iff.mpr (Finset.mem_singleton.mp hv))⟩
      left_inv := by intro i; apply e₀.injective; simp
      right_inv := by intro v; apply Subtype.ext; simp }
  refine ⟨SimpleGraph.comap e (G.1.induce (Set.compl (Set.singleton ℓ))), ?_⟩
  exact (comapIso e (G.1.induce (Set.compl (Set.singleton ℓ)))).isTree_iff.mpr htree

/-- Motifs retained at redundancy level `q`: connected tree motifs with
`1 ≤ |E(H)| ≤ q+1`, encoded by the equivalent vertex-count range for trees. -/
def RetainedMotif (q : ℕ) :=
  {H : Σ k : Fin (q + 3), TreeState k //
    1 ≤ (H.1.1 : ℕ) - 1 ∧ (H.1.1 : ℕ) - 1 ≤ q + 1}

/-- The number of ordinary subgraph copies of a retained motif in a tree.
A subgraph is counted once, rather than once per isomorphism of its vertices. -/
def motifCopies {q n : ℕ} (H : RetainedMotif q) (T : TreeState n) : ℕ :=
  let HG : TreeGraph (H.1.1 : ℕ) :=
    Quotient.out (s := treeGraphSetoid (H.1.1 : ℕ)) H.1.2
  let TG : TreeGraph n := Quotient.out (s := treeGraphSetoid n) T
  letI : Fintype TG.1.Subgraph := Fintype.ofFinite _
  letI : Fintype {S : TG.1.Subgraph // Nonempty (S.coe ≃g HG.1)} := Fintype.ofFinite _
  Fintype.card {S : TG.1.Subgraph // Nonempty (S.coe ≃g HG.1)}

/-- The joint retained motif profile of a tree. -/
def jointMotifProfile (q n : ℕ) (T : TreeState n) : RetainedMotif q → ℕ :=
  fun H => motifCopies H T

/-- The diagonal motif observable `M_H^(n)`. -/
def motifOperator {q n : ℕ} (H : RetainedMotif q) :
    TreeVector n →ₗ[ℚ] TreeVector n :=
  Finsupp.linearCombination ℚ (fun T =>
    (motifCopies H T : ℚ) • Finsupp.single T 1)

/-- The basis vector for a card, with one copy for each leaf occurrence. -/
def leafDeckBasis (m : ℕ) (T : TreeState (m + 2)) : TreeVector (m + 1) :=
  ∑ ℓ : Fin (m + 2),
    let G := Quotient.out T
    letI : Fintype {v // v ∈ G.1.neighborSet ℓ} := Fintype.ofFinite _
    if hℓ : G.1.degree ℓ = 1 then
      Finsupp.single (⟦leafCardGraph m G ℓ hℓ⟧ : TreeState (m + 1)) 1
    else 0

/-- The ordinary leaf-deck map from `m+2` vertices to `m+1` vertices. -/
def leafDeckStep (m : ℕ) : TreeVector (m + 2) →ₗ[ℚ] TreeVector (m + 1) :=
  Finsupp.linearCombination ℚ (leafDeckBasis m)

/-- The leaf-deck map `L_n`, with the vacuous small-size cases made total. -/
def leafDeck (n : ℕ) : TreeVector n →ₗ[ℚ] TreeVector (n - 1) :=
  match n with
  | 0 => 0
  | 1 => 0
  | n + 2 => by simpa using leafDeckStep n

/-- The coordinate subspace `E_λ` spanned by trees having joint profile `λ`. -/
def profileSubspace (q n : ℕ) (profile : RetainedMotif q → ℕ) :
    Submodule ℚ (TreeVector n) where
  carrier := {x | ∀ T, x T ≠ 0 → jointMotifProfile q n T = profile}
  zero_mem' := by
    intro T hT
    exact (hT (by simp)).elim
  add_mem' := by
    intro x y hx hy T hT
    by_cases hxT : x T = 0
    · apply hy T
      intro hyT
      apply hT
      simp [hxT, hyT]
    · exact hx T hxT
  smul_mem' := by
    intro c x hx T hT
    by_cases hc : c = 0
    · subst c
      simp at hT
    · apply hx T
      intro hxT
      apply hT
      simp [hxT]

/-- Injectivity of the restriction of the deck map to `E_λ`. -/
def deckRestrictionInjective (q n : ℕ) (profile : RetainedMotif q → ℕ) : Prop :=
  ∀ ⦃x z : TreeVector n⦄,
    x ∈ profileSubspace q n profile → z ∈ profileSubspace q n profile →
      leafDeck n x = leafDeck n z → x = z

/-- The motif-observability defect, written using the deck and all retained motif channels. -/
def motifObservabilityDefect (q n : ℕ) (w : TreeVector n) : Prop :=
  w ∈ LinearMap.ker (leafDeck n) ∧
    ∀ H : RetainedMotif q, motifOperator H w ∈ LinearMap.ker (leafDeck n)

/-- The sum of a finitely supported family of card-space vectors. -/
def profileVectorSum {q n : ℕ}
    (y : (RetainedMotif q → ℕ) →₀ TreeVector (n - 1)) : TreeVector (n - 1) :=
  ∑ profile ∈ y.support, y profile

/-- The motif-weighted sum of a finitely supported family of card-space vectors. -/
def profileMotifSum {q n : ℕ}
    (y : (RetainedMotif q → ℕ) →₀ TreeVector (n - 1))
    (H : RetainedMotif q) : TreeVector (n - 1) :=
  ∑ profile ∈ y.support, ((profile H : ℕ) : ℚ) • y profile

/--
Cross-profile affine circuit decomposition.  The conclusion records the profile-wise
preimages of the nonzero defect, their deck images, and the two vanishing relations.
-/
def crossProfileAffineCircuitDecomposition : Prop :=
  ∀ (q n : ℕ) (w : TreeVector n),
    (∀ profile : RetainedMotif q → ℕ, deckRestrictionInjective q n profile) →
    motifObservabilityDefect q n w → w ≠ 0 →
    ∃ (x : (RetainedMotif q → ℕ) →₀ TreeVector n)
      (y : (RetainedMotif q → ℕ) →₀ TreeVector (n - 1)),
      x ≠ 0 ∧ y ≠ 0 ∧ x.support = y.support ∧
      w = ∑ profile ∈ x.support, x profile ∧
      (∀ profile ∈ x.support,
        x profile ∈ profileSubspace q n profile ∧
        y profile = leafDeck n (x profile) ∧ y profile ≠ 0 ∧
        ∃ T : TreeState n, jointMotifProfile q n T = profile) ∧
      1 < y.support.card ∧
      profileVectorSum y = 0 ∧
      (∀ H : RetainedMotif q, profileMotifSum y H = 0)

end

end MathlibPlus.Open.Combinatorics
