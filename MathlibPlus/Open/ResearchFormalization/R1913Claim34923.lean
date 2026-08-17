import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1913

noncomputable section

/-- Three finite sets form a sunflower when their pairwise intersections
are the same common core. -/
def threeSunflower {α : Type*} [DecidableEq α]
    (X Y Z : Finset α) : Prop :=
  X ∩ Y = X ∩ Z ∧ X ∩ Y = Y ∩ Z

/-- The ordinary source-family intersection condition. -/
def pairwiseIntersectingFamily {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → (X ∩ Y).Nonempty

/-- The ordinary source-family three-sunflower-free condition, with three
distinct source members. -/
def threeSunflowerFreeFamily {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, ∀ Z ∈ F,
    X ≠ Y → X ≠ Z → Y ≠ Z →
      ¬ threeSunflower X Y Z

/-- The residual sunflower relation on three distinct occurrence indices. -/
def residualSunflower {α : Type*} [DecidableEq α]
    (A : Finset α) (B : Fin s → Finset α) (I : Fin 3 → Fin s) : Prop :=
  threeSunflower (B (I 0) \ A) (B (I 1) \ A) (B (I 2) \ A)

/-- The trace colors appearing on an indexed residual triple. -/
def residualTraceColors {α : Type*} [DecidableEq α]
    (color : Fin s → α) (I : Fin 3 → Fin s) : Finset α :=
  (Finset.univ : Finset (Fin 3)).image (fun j => color (I j))

/-- Claim 34923: exact singleton traces in an ordinary pairwise-intersecting,
three-sunflower-free uniform family produce pairwise-intersecting residual
occurrences, and a residual sunflower lifts in the one-color and three-color
cases, leaving exactly the `2+1` trace-color pattern. -/
def singletonTraceResidualColorRestriction_claim34923 : Prop :=
  ∀ (α : Type*) [DecidableEq α] (n s : ℕ)
    (F : Finset (Finset α)) (A : Finset α)
    (B : Fin s → Finset α) (color : Fin s → α),
    A ∈ F →
      (∀ X ∈ F, X.card = n) →
        pairwiseIntersectingFamily F →
          threeSunflowerFreeFamily F →
            Function.Injective B →
              (∀ i : Fin s, B i ∈ F) →
                (∀ i : Fin s,
                  color i ∈ A ∧
                    B i ∩ A = {color i} ∧
                      (B i \ A).card = n - 1 ∧
                        B i = (B i \ A) ∪ {color i}) →
                  (∀ i j : Fin s, i ≠ j →
                    (B i \ A) ≠ (B j \ A) ∨ color i ≠ color j) ∧
                    (∀ i j : Fin s, i ≠ j →
                      ((B i \ A) ∩ (B j \ A)).Nonempty) ∧
                      (∀ i : Fin s, (B i \ A).card = n - 1) ∧
                      (Finset.univ.image color).card ≤ n ∧
                      (∀ i j : Fin s, i ≠ j → color i = color j →
                        (((B i \ A) ∩ (B j \ A)).Nonempty ∧
                          ((B i \ A) ∩ (B j \ A) = ∅ →
                            threeSunflower A (B i) (B j)))) ∧
                      ∀ I : Fin 3 → Fin s, Function.Injective I →
                        residualSunflower A B I →
                          let C := residualTraceColors color I
                          (C.card = 1 →
                            (∃ a : α, ∀ j : Fin 3, color (I j) = a) ∧
                              threeSunflower (B (I 0)) (B (I 1)) (B (I 2))) ∧
                            (C.card = 3 →
                              (∀ j k : Fin 3, j ≠ k →
                                (({color (I j)} : Finset α) ∩
                                  {color (I k)} = ∅)) ∧
                                threeSunflower (B (I 0)) (B (I 1)) (B (I 2))) ∧
                            C.card = 2

end

end MathlibPlus.Open.ResearchFormalization.R1913
