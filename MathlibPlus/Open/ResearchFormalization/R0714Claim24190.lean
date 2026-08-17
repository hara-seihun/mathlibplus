import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0714Claim24190

open scoped BigOperators

noncomputable section

private def graphIsoRelation (n : ℕ) (G H : SimpleGraph (Fin n)) : Prop :=
  Nonempty (G ≃g H)

private def graphSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r := graphIsoRelation n
  iseqv :=
    { refl := fun G => ⟨SimpleGraph.Iso.refl⟩
      symm := by
        intro G H h
        rcases h with ⟨e⟩
        exact ⟨e.symm⟩
      trans := by
        intro G H K hGH hHK
        rcases hGH with ⟨e⟩
        rcases hHK with ⟨f⟩
        exact ⟨e.trans f⟩ }

private abbrev GraphType (n : ℕ) := Quotient (graphSetoid n)

private def graphTypeFinite (n : ℕ) : Finite (GraphType n) := by
  classical
  let emb : SimpleGraph (Fin n) → Finset (Sym2 (Fin n)) :=
    fun G => Finset.univ.filter (fun e => e ∈ G.edgeSet)
  letI : Finite (SimpleGraph (Fin n)) := by
    apply Finite.of_injective emb
    intro G H h
    apply SimpleGraph.ext
    funext v w
    have he : s(v, w) ∈ emb G ↔ s(v, w) ∈ emb H := by rw [h]
    simpa [emb, SimpleGraph.mem_edgeSet] using he
  apply Finite.of_surjective (Quotient.mk (graphSetoid n))
  intro q
  exact Quotient.inductionOn q (fun G => ⟨G, rfl⟩)

private noncomputable def graphTypeFintype (n : ℕ) : Fintype (GraphType n) := by
  letI : Finite (GraphType n) := graphTypeFinite n
  exact Fintype.ofFinite _

private noncomputable def graphTypeOf {n : ℕ} (G : SimpleGraph (Fin n)) : GraphType n :=
  Quotient.mk (graphSetoid n) G

private noncomputable def graphRepresentative {n : ℕ} (F : GraphType n) : SimpleGraph (Fin n) :=
  Quotient.out F

private def oneCardLabeled (n : ℕ) (F : SimpleGraph (Fin n))
    (G : SimpleGraph (Fin (n + 1))) : ℕ := by
  classical
  exact (Finset.univ.filter fun v : Fin (n + 1) =>
    Nonempty (G.induce {w : Fin (n + 1) | w ≠ v} ≃g F)).card

private noncomputable def oneCard (n : ℕ) (F : GraphType n)
    (G : GraphType (n + 1)) : ℕ :=
  oneCardLabeled n (graphRepresentative F) (graphRepresentative G)

/-- An unordered two-card deletes the selected pair and keeps its complement. -/
private def twoCardLabeled (n : ℕ) (K : SimpleGraph (Fin (n - 1)))
    (G : SimpleGraph (Fin (n + 1))) : ℕ := by
  classical
  exact ((Finset.powersetCard 2 (Finset.univ : Finset (Fin (n + 1)))).filter
    (fun S : Finset (Fin (n + 1)) =>
      Nonempty (G.induce {v : Fin (n + 1) | v ∉ S} ≃g K))).card

private noncomputable def twoCard (n : ℕ) (K : GraphType (n - 1))
    (G : GraphType (n + 1)) : ℕ :=
  twoCardLabeled n (graphRepresentative K) (graphRepresentative G)

private def extensionFiberSet (n : ℕ) (F : GraphType n) : Set (GraphType (n + 1)) :=
  {G | 0 < oneCard n F G}

private def extensionFiber (n : ℕ) (F : GraphType n) : Type :=
  {G : GraphType (n + 1) // G ∈ extensionFiberSet n F}

private noncomputable def extensionFiberFintype (n : ℕ) (F : GraphType n) :
    Fintype (extensionFiber n F) := by
  letI : Finite (GraphType (n + 1)) := graphTypeFinite (n + 1)
  letI : Fintype (GraphType (n + 1)) := Fintype.ofFinite _
  letI : Finite (extensionFiber n F) :=
    Finite.of_injective (fun G : extensionFiber n F => G.1) Subtype.val_injective
  exact Fintype.ofFinite _

private def mixedMatrix (n : ℕ) (F : GraphType n) :
    Matrix (GraphType (n - 1) × GraphType n) (extensionFiber n F) ℚ :=
  fun KP G =>
    (twoCard n KP.1 G.1 : ℚ) * (oneCard n KP.2 G.1 : ℚ)

private def ordinaryMatrix (n : ℕ) (F : GraphType n) :
    Matrix (GraphType n × GraphType n) (extensionFiber n F) ℚ :=
  fun KP G =>
    (oneCard n KP.1 G.1 : ℚ) * (oneCard n KP.2 G.1 : ℚ)

private def fullColumnRank {m k : Type*} [Fintype k]
    (M : Matrix m k ℚ) : Prop :=
  Matrix.rank M = Fintype.card k

private noncomputable def mixedFullColumnRank (n : ℕ) (F : GraphType n) : Prop := by
  letI : Fintype (GraphType (n - 1)) := graphTypeFintype (n - 1)
  letI : Fintype (GraphType n) := graphTypeFintype n
  letI : Fintype (extensionFiber n F) := extensionFiberFintype n F
  exact fullColumnRank (mixedMatrix n F)

private noncomputable def ordinaryFullColumnRank (n : ℕ) (F : GraphType n) : Prop := by
  letI : Fintype (GraphType n) := graphTypeFintype n
  letI : Fintype (extensionFiber n F) := extensionFiberFintype n F
  exact fullColumnRank (ordinaryMatrix n F)

private def edgePlusIsolatedGraph : SimpleGraph (Fin 3) where
  Adj v w := (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0)
  symm := by aesop_graph
  loopless := by aesop_graph

private def pathThreeGraph : SimpleGraph (Fin 3) where
  Adj v w :=
    (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0) ∨
      (v = 1 ∧ w = 2) ∨ (v = 2 ∧ w = 1)
  symm := by aesop_graph
  loopless := by aesop_graph

private def emptyTwo : GraphType 2 := graphTypeOf (⊥ : SimpleGraph (Fin 2))
private def completeTwo : GraphType 2 := graphTypeOf (⊤ : SimpleGraph (Fin 2))
private def emptyThree : GraphType 3 := graphTypeOf (⊥ : SimpleGraph (Fin 3))
private def completeThree : GraphType 3 := graphTypeOf (⊤ : SimpleGraph (Fin 3))
private def edgePlusIsolatedThree : GraphType 3 := graphTypeOf edgePlusIsolatedGraph
private def pathThree : GraphType 3 := graphTypeOf pathThreeGraph
private def singleton : GraphType 1 := graphTypeOf (⊥ : SimpleGraph (Fin 1))

private def orderTwoTypeMap : Fin 2 → GraphType 2 :=
  ![emptyTwo, completeTwo]

private def orderTwoRows : Fin 2 → GraphType 1 × GraphType 2 :=
  ![(singleton, emptyTwo), (singleton, completeTwo)]

private def edgelessColumns : Fin 3 → GraphType 3 :=
  ![emptyThree, edgePlusIsolatedThree, pathThree]

private def completeColumns : Fin 3 → GraphType 3 :=
  ![edgePlusIsolatedThree, pathThree, completeThree]

private def edgelessMixedDisplay : Matrix (Fin 2) (Fin 3) ℚ :=
  !![9, 6, 3; 0, 3, 6]

private def completeMixedDisplay : Matrix (Fin 2) (Fin 3) ℚ :=
  !![6, 3, 0; 3, 6, 9]

private def generatedKernel {k : Type*} [Fintype k]
    (M : Matrix (Fin 2) k ℚ) (v : k → ℚ) : Prop :=
  v ≠ 0 ∧ ∀ w, Matrix.mulVec M w = 0 ↔ ∃ c : ℚ, w = c • v

private noncomputable def exactMixedDefect (F : GraphType 2)
    (columns : Fin 3 → GraphType 3)
    (display : Matrix (Fin 2) (Fin 3) ℚ) : Prop := by
  letI : Fintype (GraphType 1) := graphTypeFintype 1
  letI : Fintype (GraphType 2) := graphTypeFintype 2
  letI : Fintype (GraphType 3) := graphTypeFintype 3
  letI : Fintype (extensionFiber 2 F) := extensionFiberFintype 2 F
  exact
    Function.Bijective orderTwoRows ∧
      ∃ h : ∀ j : Fin 3, columns j ∈ extensionFiberSet 2 F,
        Function.Bijective
            (fun j : Fin 3 =>
              (⟨columns j, h j⟩ : extensionFiber 2 F)) ∧
          (∀ i j,
            mixedMatrix 2 F (orderTwoRows i)
                (⟨columns j, h j⟩ : extensionFiber 2 F) = display i j) ∧
          Matrix.rank display = 2 ∧
          generatedKernel display (![1, -2, 1])

/-- Claim 24190: the mixed rows are not universally full-rank on the actual
one-vertex extension fibres, already for both order-two card types, while the
complete ordinary quadratic deck-product matrix remains full-rank through
order seven. -/
def mixedRowsNotUniversal_claim24190 : Prop := by
  letI : Fintype (GraphType 2) := graphTypeFintype 2
  exact
    Fintype.card (GraphType 2) = 2 ∧
      Function.Bijective orderTwoTypeMap ∧
      exactMixedDefect emptyTwo edgelessColumns edgelessMixedDisplay ∧
      exactMixedDefect completeTwo completeColumns completeMixedDisplay ∧
      ¬ mixedFullColumnRank 2 emptyTwo ∧
      ¬ mixedFullColumnRank 2 completeTwo ∧
      (∀ n : ℕ, 2 ≤ n → n ≤ 7 → ∀ F : GraphType n,
        ordinaryFullColumnRank n F)

end
end MathlibPlus.Open.ResearchFormalization.R0714Claim24190
