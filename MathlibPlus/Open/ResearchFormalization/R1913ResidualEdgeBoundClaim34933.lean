import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1913ResidualEdgeBoundClaim34933

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

private def sourceDegree {α : Type*} [DecidableEq α]
    (m : ℕ) (A : Fin m → Finset α) (y : α) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => y ∈ A i)).card

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

private def sourceTripleWitnessCount {α : Type*} [DecidableEq α]
    (m : ℕ) (A : Fin m → Finset α) (y : α) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin m))).filter
    (fun e => e.card = 3 ∧
      (e.filter (fun i => y ∈ A i)).card = 2)).card

/-- The exact two-of-three witness and both residual-hypergraph edge bounds. -/
def residualSunflowerEdgeCountBound_claim34933 : Prop :=
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
      (∀ y ∈ Y, sourceDegree m A y ≤ s) ∧
      (∑ y ∈ Y, sourceDegree m A y = m * p) ∧
      (∀ e ∈ H_Y,
        ∃ y ∈ Y,
          (e.filter (fun i => y ∈ A i)).card = 2) ∧
      (∀ y ∈ Y,
        sourceTripleWitnessCount m A y =
          Nat.choose (sourceDegree m A y) 2 *
            (m - sourceDegree m A y)) ∧
      (H_Y.card : ℚ) ≤
        ∑ y ∈ Y,
          ((Nat.choose (sourceDegree m A y) 2 *
            (m - sourceDegree m A y) : ℕ) : ℚ) ∧
      (∑ y ∈ Y,
          ((Nat.choose (sourceDegree m A y) 2 *
            (m - sourceDegree m A y) : ℕ) : ℚ)) ≤
        ((s - 1 : ℕ) : ℚ) * (p : ℚ) * (m : ℚ) ^ 2 / 2

end

end MathlibPlus.Open.ResearchFormalization.R1913ResidualEdgeBoundClaim34933
