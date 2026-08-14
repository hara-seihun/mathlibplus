import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Batch01

noncomputable section

abbrev TwoEdge (n : ℕ) := {e : Finset (Fin n) // e.card = 2}
abbrev EdgeSet (n : ℕ) := Finset (TwoEdge n)

noncomputable def edgeMap (n : ℕ) (σ : Equiv.Perm (Fin n)) (e : TwoEdge n) : TwoEdge n := by
  classical
  exact ⟨e.1.map σ.toEmbedding, by simpa using e.2⟩

noncomputable def edgeSetMap (n : ℕ) (σ : Equiv.Perm (Fin n)) (Y : EdgeSet n) : EdgeSet n := by
  classical
  exact Y.image (edgeMap n σ)

def sameEdgeType (n : ℕ) (A B : EdgeSet n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), edgeSetMap n σ A = B

noncomputable def graphOrbit (n : ℕ) (X : EdgeSet n) : Finset (EdgeSet n) := by
  classical
  exact (Finset.univ : Finset (Equiv.Perm (Fin n))).image (fun σ => edgeSetMap n σ X)

noncomputable def aX (n : ℕ) (X A : EdgeSet n) : ℚ := by
  classical
  exact ((graphOrbit n X).filter (fun Y => A ⊆ Y)).card / (graphOrbit n X).card

noncomputable def typeCountInGraph (n : ℕ) (X A : EdgeSet n) : ℕ := by
  classical
  exact (X.powerset.filter (sameEdgeType n A)).card

noncomputable def labelledTypeCount (n : ℕ) (A : EdgeSet n) : ℕ := by
  classical
  exact ((Finset.univ : Finset (EdgeSet n)).filter (sameEdgeType n A)).card

noncomputable def bX (n : ℕ) (X A B : EdgeSet n) : ℚ := by
  classical
  exact ∑ C ∈ B.powerset, (-1 : ℚ) ^ C.card * aX n X (A ∪ C)

noncomputable def containmentProbability (n : ℕ) (X A B : EdgeSet n) : ℚ := by
  classical
  exact ((graphOrbit n X).filter (fun Y => A ⊆ Y ∧ Disjoint B Y)).card /
    (graphOrbit n X).card

/-- Orbit probabilities, their type-count formula, and inclusion-exclusion. -/
def claim35818 : Prop :=
  ∀ n : ℕ, ∀ X A B : EdgeSet n,
    sameEdgeType n A B → aX n X A = aX n X B

def claim35819 : Prop :=
  ∀ n : ℕ, ∀ X A : EdgeSet n,
    aX n X A =
      (typeCountInGraph n X A : ℚ) / (labelledTypeCount n A : ℚ)

def claim35821 : Prop :=
  ∀ n : ℕ, ∀ X A B : EdgeSet n, Disjoint A B →
    bX n X A B = containmentProbability n X A B

def claim35822 : Prop :=
  (∀ n : ℕ, ∀ X A B : EdgeSet n, Disjoint A B → 0 ≤ bX n X A B) ∧
    (∀ k n : ℕ, ∀ X A B : EdgeSet n,
      Disjoint A B → A.card + B.card ≤ k → 0 ≤ bX n X A B)

abbrev IncidenceIndex (n : ℕ) (𝒜 : Finset (EdgeSet n)) :=
  {A : EdgeSet n // A ∈ 𝒜}

def incidenceVector (n : ℕ) (𝒜 : Finset (EdgeSet n)) (Y : EdgeSet n) :
    IncidenceIndex n 𝒜 → ℝ := by
  classical
  exact fun A => if A.1 ⊆ Y then 1 else 0

def outerProduct {ι : Type} (v w : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => v i * w j

noncomputable def QX (n : ℕ) (X : EdgeSet n) (𝒜 : Finset (EdgeSet n)) :
    Matrix (IncidenceIndex n 𝒜) (IncidenceIndex n 𝒜) ℝ := by
  classical
  exact ((graphOrbit n X).card : ℝ)⁻¹ •
    ∑ Y ∈ graphOrbit n X, outerProduct (incidenceVector n 𝒜 Y) (incidenceVector n 𝒜 Y)

def PositiveSemidefinite {ι : Type} [Fintype ι] (Q : Matrix ι ι ℝ) : Prop :=
  ∀ z : ι → ℝ, 0 ≤ ∑ i, ∑ j, z i * Q i j * z j

def CompletelyPositive {ι : Type} [Fintype ι] (Q : Matrix ι ι ℝ) : Prop :=
  ∃ m : ℕ, ∃ W : Fin m → ι → ℝ,
    (∀ k i, 0 ≤ W k i) ∧
      Q = ∑ k, outerProduct (W k) (W k)

def claim35826 : Prop :=
  ∀ n : ℕ, ∀ X : EdgeSet n, ∀ 𝒜 : Finset (EdgeSet n),
    QX n X 𝒜 =
      ((graphOrbit n X).card : ℝ)⁻¹ •
        ∑ Y ∈ graphOrbit n X,
          outerProduct (incidenceVector n 𝒜 Y) (incidenceVector n 𝒜 Y) ∧
    PositiveSemidefinite (QX n X 𝒜) ∧
    CompletelyPositive (QX n X 𝒜)

end
end MathlibPlus.Open.ResearchFormalization.Batch01
