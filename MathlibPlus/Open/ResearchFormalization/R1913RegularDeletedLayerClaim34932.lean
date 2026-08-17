import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1913RegularDeletedLayerClaim34932

noncomputable section

open Classical

private def threeSunflower {α : Type*} [DecidableEq α]
    (X Y Z : Finset α) : Prop :=
  X ∩ Y = X ∩ Z ∧ X ∩ Y = Y ∩ Z

private def sourceThreeSunflowerFree {α : Type*} [DecidableEq α]
    (A : Fin m → Finset α) : Prop :=
  ∀ i j k : Fin m,
    i ≠ j → i ≠ k → j ≠ k →
    ¬ threeSunflower (A i) (A j) (A k)

private def residualSunflower {α : Type*} [DecidableEq α]
    (B : Fin m → Finset α) (i j k : Fin m) : Prop :=
  threeSunflower (B i) (B j) (B k)

private def residualHyperedge {α : Type*} [DecidableEq α]
    (B : Fin m → Finset α) (e : Finset (Fin m)) : Prop :=
  e.card = 3 ∧
    ∃ i j k : Fin m,
      i ∈ e ∧ j ∈ e ∧ k ∈ e ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      residualSunflower B i j k

private def residualHypergraph {α : Type*} [DecidableEq α]
    (B : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (residualHyperedge B)

/-- The regular literal deletion and its exact residual 3-uniform hypergraph. -/
def regularDeletedLayerResidualHypergraph_claim34932 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (m r p s : ℕ)
    (A : Fin m → Finset α) (Y : Finset α),
    Function.Injective A →
    (∀ i : Fin m, (A i).card = r) →
    sourceThreeSunflowerFree A →
    (∀ i : Fin m, (A i ∩ Y).card = p) →
    (∀ y ∈ Y,
      (Finset.univ.filter (fun i : Fin m => y ∈ A i)).card ≤ s) →
    let n := r - p
    let B : Fin m → Finset α := fun i => A i \ Y
    let H_Y := residualHypergraph B
    (∀ i : Fin m, (B i).card = n) ∧
      (∀ e ∈ H_Y, e.card = 3) ∧
      (∀ e : Finset (Fin m),
        e ∈ H_Y ↔
          e.card = 3 ∧
            ∃ i j k : Fin m,
              i ∈ e ∧ j ∈ e ∧ k ∈ e ∧
              i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
              residualSunflower B i j k)

end

end MathlibPlus.Open.ResearchFormalization.R1913RegularDeletedLayerClaim34932
