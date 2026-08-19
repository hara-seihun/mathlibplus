import MathlibPlus.Open.FormalizationBatch.SetSystems

namespace MathlibPlus.Open.ResearchFormalization.R1840Claim32812

noncomputable section

open MathlibPlus.Open.FormalizationBatch.SetSystems

/-- The exact residual family in a fixed trace class, excluding the pivot. -/
def exactTraceResidual32812 {α : Type}
    (F : Set (Set α)) (A T : Set α) : Set (Set α) :=
  (fun B : Set α => B \ A) ''
    {B | B ∈ F ∧ B ≠ A ∧ A ∩ B = T}

/-- The uniform and sunflower-free predicates of the general residual carrier. -/
def uniformFamily32812 {α : Type}
    (F : Set (Set α)) (n : ℕ) : Prop :=
  ∀ B, B ∈ F → B.Finite ∧ Set.ncard B = n

def sunflowerFamily32812 {α : Type}
    (F : Set (Set α)) : Prop :=
  ∃ C : Set α,
    ∀ ⦃B₁ B₂ : Set α⦄,
      B₁ ∈ F → B₂ ∈ F → B₁ ≠ B₂ → B₁ ∩ B₂ = C

def sunflowerFree32812 {α : Type}
    (F : Set (Set α)) (k : ℕ) : Prop :=
  ¬ ∃ S : Set (Set α),
    S.Finite ∧ Set.ncard S = k ∧ S ⊆ F ∧ sunflowerFamily32812 S

/-- The exact matching-number conclusion, with the source's fixed `k ≥ 3`
scope and residual cardinality/injectivity carrier. -/
def generalResidualMatchingBound32812 : Prop :=
  ∀ {α : Type} (F : Set (Set α)) (n k : ℕ),
    3 ≤ k →
      uniformFamily32812 F n →
        sunflowerFree32812 F k →
          ∀ A, A ∈ F →
            ∀ T : Set α, T ⊂ A →
              ¬ ∃ R : Fin (k - 1) → Set α,
                (∀ i : Fin (k - 1), R i ∈ exactTraceResidual32812 F A T) ∧
                  (∀ ⦃i j : Fin (k - 1)⦄, i ≠ j → R i ≠ R j) ∧
                  (∀ ⦃i j : Fin (k - 1)⦄, i ≠ j →
                    Disjoint (R i) (R j))

/-- Pairwise intersection is exactly the matching-number-at-most-one
specialization of the residual condition. -/
def pairwiseIntersectionSpecialization32812 : Prop :=
  ∀ {α : Type} (F : Set (Set α)),
    (∀ ⦃B₁ B₂ : Set α⦄,
      B₁ ∈ F → B₂ ∈ F → B₁ ≠ B₂ → ¬ Disjoint B₁ B₂) ↔
      ¬ ∃ R : Fin 2 → Set α,
        (∀ i : Fin 2, R i ∈ F) ∧
          (∀ ⦃i j : Fin 2⦄, i ≠ j → R i ≠ R j) ∧
          (∀ ⦃i j : Fin 2⦄, i ≠ j → Disjoint (R i) (R j))

/-- The displayed three-petal `k=4` witness. -/
def witnessA : Finset (Fin 6) := {1, 2}
def witnessB : Finset (Fin 6) := {3, 4}
def witnessC : Finset (Fin 6) := {5, 6}
def witnessFamily : Finset (Finset (Fin 6)) :=
  {witnessA, witnessB, witnessC}

def witnessExactTraceResidual :
    Finset (Finset (Fin 6)) :=
  (witnessFamily.filter (fun S =>
    S ≠ witnessA ∧ witnessA ∩ S = (∅ : Finset (Fin 6)))).image
      (fun S => S \ witnessA)

/-- Claim 32812: the general matching-number residual condition is scoped to
`k ≥ 3`, pairwise intersection is only its `k=3` specialization, and the
three displayed disjoint petals give the exact `k=4` obstruction. -/
def claim32812 : Prop :=
  generalResidualMatchingBound32812 ∧
    pairwiseIntersectionSpecialization32812 ∧
    ¬ containsSunflower witnessFamily 4 ∧
    witnessExactTraceResidual = {witnessB, witnessC} ∧
    Disjoint (witnessB : Set (Fin 6)) (witnessC : Set (Fin 6))

end

end MathlibPlus.Open.ResearchFormalization.R1840Claim32812
