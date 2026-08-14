import Mathlib

namespace MathlibPlus.Open.Graphs

noncomputable def graphIsoSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r G H := Nonempty (G ≃g H)
  iseqv := by
    constructor
    · intro G
      exact ⟨RelIso.refl G.Adj⟩
    · intro G H h
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    · intro G H K hGH hHK
      rcases hGH with ⟨e⟩
      rcases hHK with ⟨f⟩
      exact ⟨SimpleGraph.Iso.comp f e⟩

abbrev GraphIsoClass (n : ℕ) := Quotient (graphIsoSetoid n)

noncomputable instance graphIsoClassFintype (n : ℕ) : Fintype (GraphIsoClass n) :=
  Fintype.ofFinite _

def graphAut (G : SimpleGraph (Fin n)) :=
  { e : Equiv (Fin n) (Fin n) // ∀ v w, G.Adj (e v) (e w) ↔ G.Adj v w }

noncomputable def graphAutConj {n : ℕ} {G H : SimpleGraph (Fin n)}
    (e : G ≃g H) : graphAut G ≃ graphAut H :=
  { toFun := fun f =>
      ⟨e.toEquiv.symm.trans (f.1.trans e.toEquiv), by
        intro v w
        change H.Adj (e.toEquiv (f.1 (e.toEquiv.symm v)))
            (e.toEquiv (f.1 (e.toEquiv.symm w))) ↔ H.Adj v w
        calc
          _ ↔ G.Adj (f.1 (e.toEquiv.symm v)) (f.1 (e.toEquiv.symm w)) := e.map_rel_iff'
          _ ↔ G.Adj (e.toEquiv.symm v) (e.toEquiv.symm w) := f.2 _ _
          _ ↔ H.Adj v w := by
            simpa only [Equiv.apply_symm_apply] using
              (e.map_rel_iff' (a := e.toEquiv.symm v)
                (b := e.toEquiv.symm w)).symm⟩
    invFun := fun g =>
      ⟨e.toEquiv.trans (g.1.trans e.toEquiv.symm), by
        intro v w
        change G.Adj (e.toEquiv.symm (g.1 (e.toEquiv v)))
            (e.toEquiv.symm (g.1 (e.toEquiv w))) ↔ G.Adj v w
        calc
          _ ↔ H.Adj (g.1 (e.toEquiv v)) (g.1 (e.toEquiv w)) := by
            simpa only [Equiv.apply_symm_apply] using
              (e.map_rel_iff' (a := e.toEquiv.symm (g.1 (e.toEquiv v)))
                (b := e.toEquiv.symm (g.1 (e.toEquiv w)))).symm
          _ ↔ H.Adj (e.toEquiv v) (e.toEquiv w) := g.2 _ _
          _ ↔ G.Adj v w := e.map_rel_iff'⟩
    left_inv := by
      intro f
      apply Subtype.ext
      apply Equiv.ext
      intro v
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    right_inv := by
      intro g
      apply Subtype.ext
      apply Equiv.ext
      intro v
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply] }

noncomputable instance graphAutFintype {n : ℕ} (G : SimpleGraph (Fin n)) : Fintype (graphAut G) := by
  classical
  letI : Fintype (Equiv (Fin n) (Fin n)) := Fintype.ofFinite _
  let s : Finset (Equiv (Fin n) (Fin n)) :=
    Finset.univ.filter (fun x => ∀ v w, G.Adj (x v) (x w) ↔ G.Adj v w)
  exact Fintype.subtype s (by simp [s])

noncomputable def graphAutCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Fintype.card (graphAut G)

noncomputable def graphAutWeight (n : ℕ) : GraphIsoClass n → ℚ :=
  Quotient.lift (fun G => (graphAutCount G : ℚ)) (by
    intro G H h
    rcases h with ⟨e⟩
    change (Fintype.card (graphAut G) : ℚ) = Fintype.card (graphAut H)
    exact_mod_cast Fintype.card_congr (graphAutConj e))

noncomputable def graphClass {n : ℕ} (G : SimpleGraph (Fin n)) : GraphIsoClass n :=
  Quotient.mk (graphIsoSetoid n) G

noncomputable def graphRepresentative {n : ℕ} (G : GraphIsoClass n) : SimpleGraph (Fin n) :=
  Quotient.out G

def deleteGraph {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    SimpleGraph (Fin n) :=
  G.comap (Fin.succAbove v)

def insertGraph {n : ℕ} (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun i j =>
    Fin.lastCases
      (Fin.lastCases False (fun j' => j' ∈ S) j)
      (fun i' => Fin.lastCases (i' ∈ S) (fun j' => H.Adj i' j') j)
      i)

noncomputable def deletionMultiplicity {n : ℕ} (G : GraphIsoClass (n + 1))
    (H : GraphIsoClass n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v =>
    graphClass (deleteGraph (graphRepresentative G) v) = H)).card

noncomputable def insertionMultiplicity {n : ℕ} (H : GraphIsoClass n)
    (G : GraphIsoClass (n + 1)) : ℕ := by
  classical
  exact ((Finset.powerset (Finset.univ : Finset (Fin n))).filter (fun S =>
    graphClass (insertGraph (graphRepresentative H) S) = G)).card

noncomputable def deckIntegerMatrix (n : ℕ) :
    Matrix (GraphIsoClass n) (GraphIsoClass (n + 1)) ℤ :=
  fun H G => deletionMultiplicity G H

noncomputable def insertIntegerMatrix (n : ℕ) :
    Matrix (GraphIsoClass (n + 1)) (GraphIsoClass n) ℤ :=
  fun G H => insertionMultiplicity H G

noncomputable def deckMatrix (n : ℕ) :
    Matrix (GraphIsoClass n) (GraphIsoClass (n + 1)) ℚ :=
  fun H G => deletionMultiplicity G H

noncomputable def insertMatrix (n : ℕ) :
    Matrix (GraphIsoClass (n + 1)) (GraphIsoClass n) ℚ :=
  fun G H => insertionMultiplicity H G

noncomputable def automorphismDiagonal (n : ℕ) :
    Matrix (GraphIsoClass n) (GraphIsoClass n) ℚ := by
  classical
  exact Matrix.diagonal (graphAutWeight n)

/-- Claim 5002: the raw basis transpose is not the weighted adjoint. -/
def basisTransposeIsNotAdjoint : Prop :=
  (¬ (∀ n : ℕ, deckIntegerMatrix n = (insertIntegerMatrix n).transpose)) ∧
    (∀ n : ℕ,
      automorphismDiagonal n * deckMatrix n =
        (insertMatrix n).transpose * automorphismDiagonal (n + 1))

end MathlibPlus.Open.Graphs
