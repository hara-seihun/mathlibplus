import Mathlib

namespace MathlibPlus.Open.Probability

open scoped BigOperators

noncomputable section

/--
For every finite weighted two-level pure-selector incidence graph, the exact
uniform variance of the selector mixture is paid for by a private or shared
coordinate with the sharp factor `3/2`. The final conjunct records the
parallel two-edge equality witness.
-/
def pureSelectorGraphDepthTwoThreeHalvesSaving : Prop :=
  ∀ (m p : ℕ) (u v : Fin m → Fin p) (weights : Fin m → ℝ),
    (∀ e, u e ≠ v e) →
    (∀ e, 0 ≤ weights e) →
    (∑ e, weights e = 1) →
    let sign : Bool → ℝ := fun b => if b then 1 else -1
    let target : (Fin m → Bool) → (Fin p → Bool) → Fin m → ℝ :=
      fun x y e => if x e then sign (y (v e)) else sign (y (u e))
    let mixture : (Fin m → Bool) → (Fin p → Bool) → ℝ :=
      fun x y => ∑ e, weights e * target x y e
    let average :
        ((Fin m → Bool) → (Fin p → Bool) → ℝ) → ℝ :=
      fun f =>
        (1 / (Fintype.card (Fin m → Bool) : ℝ)) *
          (1 / (Fintype.card (Fin p → Bool) : ℝ)) *
          ∑ x, ∑ y, f x y
    let mean : ℝ := average mixture
    let variance : ℝ := average (fun x y => (mixture x y - mean) ^ 2)
    let sharedLoad : Fin p → ℝ := fun w =>
      (1 / 2 : ℝ) *
        ∑ e, if u e = w ∨ v e = w then weights e else 0
    ((∃ e, variance ≤ (3 / 2 : ℝ) * weights e) ∨
      (∃ w, variance ≤ (3 / 2 : ℝ) * sharedLoad w)) ∧
    (let m : ℕ := 2
     let p : ℕ := 2
     let u : Fin m → Fin p := fun _ => 0
     let v : Fin m → Fin p := fun _ => 1
     let weights : Fin m → ℝ := fun _ => 1 / 2
     let sign : Bool → ℝ := fun b => if b then 1 else -1
     let target : (Fin m → Bool) → (Fin p → Bool) → Fin m → ℝ :=
       fun x y e => if x e then sign (y (v e)) else sign (y (u e))
     let mixture : (Fin m → Bool) → (Fin p → Bool) → ℝ :=
       fun x y => ∑ e, weights e * target x y e
     let average :
         ((Fin m → Bool) → (Fin p → Bool) → ℝ) → ℝ :=
       fun f =>
         (1 / (Fintype.card (Fin m → Bool) : ℝ)) *
           (1 / (Fintype.card (Fin p → Bool) : ℝ)) *
           ∑ x, ∑ y, f x y
     let mean : ℝ := average mixture
     let variance : ℝ := average (fun x y => (mixture x y - mean) ^ 2)
     let sharedLoad : Fin p → ℝ := fun w =>
       (1 / 2 : ℝ) *
         ∑ e, if u e = w ∨ v e = w then weights e else 0
     (∀ e, u e ≠ v e) ∧
       (∀ e, 0 ≤ weights e) ∧
       (∑ e, weights e = 1) ∧
       variance = 3 / 4 ∧
       (∀ e, weights e = 1 / 2) ∧
       (∀ w, sharedLoad w = 1 / 2))

end

end MathlibPlus.Open.Probability
