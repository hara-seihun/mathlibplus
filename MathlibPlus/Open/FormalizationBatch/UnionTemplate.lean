import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.UnionTemplate

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
open Set

/-- The fixed roots and absent-root template sets on `[9]`. -/
def rootCoordinates : Finset (Fin 9) := {0, 1, 2}
def R₁ : Finset (Fin 9) := {1, 3, 4}
def R₂ : Finset (Fin 9) := {2, 5, 6}

def unionClosedFamily (F : Finset (Finset (Fin 9))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F

def incidenceColumn (F : Finset (Finset (Fin 9))) (i : Fin 9) :
    Finset (Finset (Fin 9)) :=
  F.filter (fun A => i ∈ A)

def everyCoordinateOccurs (F : Finset (Finset (Fin 9))) : Prop :=
  ∀ i, ∃ A ∈ F, i ∈ A

def pairwiseDistinctColumns (F : Finset (Finset (Fin 9))) : Prop :=
  ∀ i j, i ≠ j → incidenceColumn F i ≠ incidenceColumn F j

def traceMultiplicity (F : Finset (Finset (Fin 9)))
    (T : Finset (Fin 9)) : ℕ :=
  (F.filter (fun A => A ∩ rootCoordinates = T)).card

/-- Claim 42295. -/
def claim42295 (F : Finset (Finset (Fin 9))) : Prop :=
  F.card = 53 ∧ unionClosedFamily F ∧ ∅ ∈ F ∧
  everyCoordinateOccurs F ∧ pairwiseDistinctColumns F ∧
  (∀ A ∈ F, A.Nonempty → 3 ≤ A.card) ∧
  (∀ i, i = 0 ∨ i = 1 ∨ i = 2 →
    (F.filter (fun A => i ∈ A)).card = 26) ∧
  (∀ T ∈ rootCoordinates.powerset, 3 ≤ traceMultiplicity F T) ∧
  R₁ ∉ F ∧ R₂ ∉ F ∧ R₁ ∪ R₂ ∈ F ∧
  unionClosedFamily (F ∪ {R₁}) ∧ unionClosedFamily (F ∪ {R₂})

def outsideCoordinates : Finset (Fin 9) :=
  Finset.univ.filter (fun i => 3 ≤ i.1 ∧ i.1 ≤ 8)

def coordinateFrequency (F : Finset (Finset (Fin 9))) (i : Fin 9) : ℕ :=
  (F.filter (fun A => i ∈ A)).card

def m9 (F : Finset (Finset (Fin 9))) : ℕ :=
  outsideCoordinates.sup (coordinateFrequency F)

noncomputable def M9 : ℕ :=
  sInf {k : ℕ | ∃ F : Finset (Finset (Fin 9)), claim42295 F ∧ m9 F = k}

/-- Claim 42296. -/
def claim42296 : Prop :=
  (∀ F, claim42295 F →
    m9 F = outsideCoordinates.sup (coordinateFrequency F)) ∧
  M9 = sInf {k : ℕ | ∃ F : Finset (Finset (Fin 9)), claim42295 F ∧ m9 F = k}

/-- Claim 42298. -/
def claim42298 : Prop :=
  (¬ ∃ F : Finset (Finset (Fin 9)), claim42295 F ∧ m9 F ≤ 26) ∧
  M9 ≥ 27

/-- Claim 42299. -/
def claim42299 : Prop :=
  ∃ F₄₀ : Finset (Finset (Fin 9)),
    claim42295 F₄₀ ∧
    (∀ i : Fin 9,
      coordinateFrequency F₄₀ i =
        if i = 0 then 26 else if i = 1 then 26 else if i = 2 then 26
        else if i = 3 then 36 else if i = 4 then 39 else if i = 5 then 40
        else if i = 6 then 39 else if i = 7 then 36 else 1) ∧
    m9 F₄₀ = 40 ∧ M9 ≤ 40

/-- Claim 42300. -/
def claim42300 : Prop := 27 ≤ M9 ∧ M9 ≤ 40

def unionClosedFamilyGeneric {α : Type}
    (D : Finset (Finset α)) : Prop :=
  ∀ A ∈ D, ∀ B ∈ D, A ∪ B ∈ D

def actualGroundFamily {α : Type}
    (G : Finset α) (n : ℕ) (D : Finset (Finset α)) : Prop :=
  G.card = n ∧
  (∀ A ∈ D, A ⊆ G) ∧
  (∀ x ∈ G, ∃ A ∈ D, x ∈ A)

def separatingFamily {α : Type}
    (G : Finset α) (D : Finset (Finset α)) : Prop :=
  ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
    ∃ A ∈ D, (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)

def coordinateFrequencyOn {α : Type}
    (D : Finset (Finset α)) (x : α) : ℕ :=
  (D.filter (fun A => x ∈ A)).card

/-- Claim 42313. -/
def claim42313 : Prop :=
  ∀ {α : Type} (G : Finset α) (n : ℕ) (D : Finset (Finset α)),
    actualGroundFamily G n D →
    unionClosedFamilyGeneric D →
    separatingFamily G D →
    ∃ x ∈ G, coordinateFrequencyOn D x ≥ n

end
end MathlibPlus.Open.FormalizationBatch.UnionTemplate
