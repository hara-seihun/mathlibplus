import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffedd

abbrev LabeledGraph (n : ℕ) := SimpleGraph (Fin n)

def graphSetoid (n : ℕ) : Setoid (LabeledGraph n) where
  r G H := Nonempty (G ≃g H)
  iseqv := by
    constructor
    · intro G
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro G H h
      rcases h with ⟨i⟩
      exact ⟨i.symm⟩
    · intro G H K h₁ h₂
      rcases h₁ with ⟨i⟩
      rcases h₂ with ⟨j⟩
      exact ⟨RelIso.trans i j⟩

abbrev UnlabeledGraph (n : ℕ) := Quotient (graphSetoid n)

noncomputable instance unlabeledGraphFintype (n : ℕ) : Fintype (UnlabeledGraph n) :=
  Fintype.ofFinite _

noncomputable def graphEdgeCount {n : ℕ} (G : LabeledGraph n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ G.Adj p.1 p.2)).card

noncomputable def graphAutomorphismCount {n : ℕ} (G : LabeledGraph n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : Equiv.Perm (Fin n) =>
    ∀ v w, G.Adj v w ↔ G.Adj (e v) (e w))).card

noncomputable def omegaWeight (n : ℕ) (G : LabeledGraph n) : ℚ :=
  ((-1 : ℚ) ^ graphEdgeCount G) * (Nat.factorial n : ℚ) /
    (graphAutomorphismCount G : ℚ)

def GraphInvariant {n : ℕ} (f : LabeledGraph n → ℚ) : Prop :=
  ∀ ⦃G H⦄, Nonempty (G ≃g H) → f G = f H

noncomputable def omegaPairing (n : ℕ) (f : LabeledGraph n → ℚ) : ℚ :=
  ∑ q : UnlabeledGraph n, omegaWeight n (Quotient.out q) * f (Quotient.out q)

noncomputable def omegaClassPairing (n : ℕ) (f : UnlabeledGraph n → ℚ) : ℚ :=
  ∑ q : UnlabeledGraph n, omegaWeight n (Quotient.out q) * f q

def claim21006 : Prop :=
  ∀ (n : ℕ) (f : LabeledGraph n → ℚ),
    GraphInvariant f →
      omegaPairing n f =
        ∑ G : LabeledGraph n, ((-1 : ℚ) ^ graphEdgeCount G) * f G

def deleteVertex (k : ℕ) (G : LabeledGraph (k + 1)) (v : Fin (k + 1)) : LabeledGraph k :=
  SimpleGraph.comap (Fin.succAbove v) G

noncomputable def cardClass (k : ℕ) (G : LabeledGraph (k + 1)) (v : Fin (k + 1)) :
    UnlabeledGraph k :=
  Quotient.mk'' (deleteVertex k G v)

noncomputable def deckMultiplicity (k : ℕ) (F : UnlabeledGraph k)
    (G : UnlabeledGraph (k + 1)) : ℚ := by
  classical
  exact ((Finset.univ.filter (fun v : Fin (k + 1) =>
    cardClass k (Quotient.out G) v = F)).card : ℚ)

noncomputable def deckCoordinate (k : ℕ) (F : UnlabeledGraph k) :
    UnlabeledGraph (k + 1) → ℚ :=
  fun G => deckMultiplicity k F G

def deckQuadratic (k : ℕ) :
    Submodule ℚ (UnlabeledGraph (k + 1) → ℚ) :=
  Submodule.span ℚ {p : UnlabeledGraph (k + 1) → ℚ |
    p = (fun _ => 1) ∨
    (∃ F, p = deckCoordinate k F) ∨
    (∃ F H, p = fun G => deckCoordinate k F G * deckCoordinate k H G)}

def deckCubic (k : ℕ) :
    Submodule ℚ (UnlabeledGraph (k + 1) → ℚ) :=
  Submodule.span ℚ {p : UnlabeledGraph (k + 1) → ℚ |
    p = (fun _ => 1) ∨
    (∃ F, p = deckCoordinate k F) ∨
    (∃ F H, p = fun G => deckCoordinate k F G * deckCoordinate k H G) ∨
    (∃ F H I, p = fun G =>
      deckCoordinate k F G * deckCoordinate k H G * deckCoordinate k I G)}

def claim21007 : Prop :=
  (∀ (k : ℕ), 1 ≤ k →
    ∀ f : UnlabeledGraph (k + 1) → ℚ,
      f ∈ deckQuadratic k → omegaClassPairing (k + 1) f = 0) ∧
  omegaClassPairing 1 (fun _ => 1) = 1

def claim21010 : Prop :=
  Fintype.card (UnlabeledGraph 5) = 34 ∧
  Fintype.card (UnlabeledGraph 6) = 156 ∧
  Fintype.card (UnlabeledGraph 7) = 1044 ∧
  Module.finrank ℚ (deckQuadratic 4) = 33 ∧
  Module.finrank ℚ (deckQuadratic 5) = 155 ∧
  Module.finrank ℚ (deckQuadratic 6) = 1043 ∧
  Module.finrank ℚ ((UnlabeledGraph 5 → ℚ) ⧸ deckQuadratic 4) = 1 ∧
  Module.finrank ℚ ((UnlabeledGraph 6 → ℚ) ⧸ deckQuadratic 5) = 1 ∧
  Module.finrank ℚ ((UnlabeledGraph 7 → ℚ) ⧸ deckQuadratic 6) = 1 ∧
  (∀ f : UnlabeledGraph 5 → ℚ,
    f ∈ deckQuadratic 4 ↔ omegaClassPairing 5 f = 0) ∧
  (∀ f : UnlabeledGraph 6 → ℚ,
    f ∈ deckQuadratic 5 ↔ omegaClassPairing 6 f = 0) ∧
  (∀ f : UnlabeledGraph 7 → ℚ,
    f ∈ deckQuadratic 6 ↔ omegaClassPairing 7 f = 0) ∧
  (∃ f : UnlabeledGraph 5 → ℚ, omegaClassPairing 5 f ≠ 0) ∧
  (∃ f : UnlabeledGraph 6 → ℚ, omegaClassPairing 6 f ≠ 0) ∧
  (∃ f : UnlabeledGraph 7 → ℚ, omegaClassPairing 7 f ≠ 0)

def claim21014 : Prop :=
  Module.finrank ℚ (deckCubic 3) = 11 ∧
  Module.finrank ℚ (deckCubic 4) = 34 ∧
  Module.finrank ℚ (deckCubic 5) = 156 ∧
  Module.finrank ℚ (deckCubic 6) = 1044

def claim21016 : Prop :=
  Fintype.card (UnlabeledGraph 1) = 1 ∧
  (∀ q : UnlabeledGraph 1, omegaWeight 1 (Quotient.out q) = 1) ∧
  omegaClassPairing 1 (fun _ => 1) = 1 ∧
  (∀ (k : ℕ), 1 ≤ k →
    ∀ f : UnlabeledGraph (k + 1) → ℚ,
      f ∈ deckQuadratic k → omegaClassPairing (k + 1) f = 0) ∧
  ¬ (∀ (k : ℕ),
    ∀ f : UnlabeledGraph (k + 1) → ℚ,
      f ∈ deckQuadratic k → omegaClassPairing (k + 1) f = 0)

end MathlibPlus.Open.ResearchFormalization.Batch019ffedd
