import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatchR0665

noncomputable section

def GraphIso {V W : Type} (X : SimpleGraph V) (Y : SimpleGraph W) : Prop :=
  Nonempty (X ≃g Y)

def graphSetoid (n : ℕ) : Setoid (SimpleGraph (Fin n)) where
  r X Y := GraphIso X Y
  iseqv :=
    { refl := fun X => ⟨SimpleGraph.Iso.refl⟩
      symm := fun {X Y} h => h.elim (fun f => ⟨f.symm⟩)
      trans := fun {X Y Z} h₁ h₂ =>
        h₁.elim (fun f₁ => h₂.elim (fun f₂ => ⟨RelIso.trans f₁ f₂⟩)) }

def GraphClass (n : ℕ) := Quotient (graphSetoid n)

def deleteVertex {V : Type} (X : SimpleGraph V) (a : V) : SimpleGraph {x : V // x ≠ a} :=
  X.induce {x : V | x ≠ a}

def deletePair {V : Type} (X : SimpleGraph V) (v w : V) :
    SimpleGraph {x : V // x ≠ v ∧ x ≠ w} :=
  X.induce {x : V | x ≠ v ∧ x ≠ w}

noncomputable def oneCardMultiplicity
    {V W : Type} [Fintype V]
    (X : SimpleGraph V) (P : SimpleGraph W) : ℕ := by
  classical
  exact Fintype.card {a : V // GraphIso (deleteVertex X a) P}

noncomputable def twoCardMultiplicity
    {V W : Type} [Fintype V]
    (X : SimpleGraph V) (K : SimpleGraph W) : ℕ := by
  classical
  exact Fintype.card
    {s : Finset V // s.card = 2 ∧
      GraphIso (X.induce {x : V | x ∉ s}) K}

/-- The unlabelled one-vertex extension fibre of a graph of order `m`. -/
def oneVertexExtensionFibre
    {m : ℕ} (F : SimpleGraph (Fin m)) : Set (GraphClass (m + 1)) :=
  {q | ∃ G : SimpleGraph (Fin (m + 1)),
    Quotient.mk (graphSetoid (m + 1)) G = q ∧
    ∃ a : Fin (m + 1), GraphIso (deleteVertex G a) F}

/-- Four distinct vertices witness the three deletion occurrences in an
`F`-transverse occurrence. -/
def hasFTransverseOccurrence
    {m : ℕ}
    (G : SimpleGraph (Fin (m + 1)))
    (F P : SimpleGraph (Fin m))
    (K : SimpleGraph (Fin (m - 1))) : Prop :=
  ∃ a u v w : Fin (m + 1),
    a ≠ u ∧ a ≠ v ∧ a ≠ w ∧
    u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
    GraphIso (deleteVertex G a) F ∧
    GraphIso (deleteVertex G u) P ∧
    GraphIso (deletePair G v w) K

/-- The support of the product of the two-deletion and one-deletion
multiplicities, restricted to the extension fibre. -/
def mixedSupport
    {m : ℕ}
    (F P : SimpleGraph (Fin m))
    (K : SimpleGraph (Fin (m - 1))) : Set (GraphClass (m + 1)) :=
  {q | ∃ G : SimpleGraph (Fin (m + 1)),
    Quotient.mk (graphSetoid (m + 1)) G = q ∧
    (∃ a : Fin (m + 1), GraphIso (deleteVertex G a) F) ∧
    0 < twoCardMultiplicity G K ∧
    0 < oneCardMultiplicity G P}

/-- The three exclusions defining transverse purity. -/
def transversePure
    {m : ℕ}
    (F P : SimpleGraph (Fin m))
    (K : SimpleGraph (Fin (m - 1))) : Prop :=
  ¬ GraphIso P F ∧
  oneCardMultiplicity F K = 0 ∧
  oneCardMultiplicity P K = 0

end

end MathlibPlus.Open.Research.FormalizationBatchR0665
