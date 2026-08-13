import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
A sharp depth-two theorem for the shared-centre star family.  Component `i`
uses a private root and private leaf, and chooses between that leaf and one
shared centre coordinate.  The proposition uses the exact finite-cube
root-inclusive posterior-variance area of a complete fresh-coordinate policy.
-/
def sharedCenterStarDepthTwoOracleArea : Prop :=
  ∀ (m : ℕ), 0 < m →
    ∀ (w : Fin m → ℝ),
      (∀ i, 0 ≤ w i) →
      (∑ i, w i) = 1 →
      let Ω := (Fin (m + 1) ⊕ Fin m) → Bool
      let Strategy := List Bool → Ω
      let transcript : Strategy → Ω → ℕ → List Bool := fun q x t =>
        Nat.rec [] (fun _ answers => answers ++ [x (q answers)]) t
      let Fresh : Strategy → Prop := fun q =>
        ∀ (x : Ω) (a b : ℕ), a < b → b < Fintype.card Ω →
          q (transcript q x a) ≠ q (transcript q x b)
      let sgn : Bool → ℝ := fun b => if b then 1 else -1
      let target : Ω → ℝ := fun x =>
        ∑ i, w i * sgn (if x (Sum.inl i.succ)
          then x (Sum.inr i)
          else x (Sum.inl (0 : Fin (m + 1))))
      let cell : Strategy → Ω → ℕ → Finset Ω := fun q x t =>
        Finset.univ.filter (fun y => transcript q y t = transcript q x t)
      let mean : Strategy → (Ω → ℝ) → Ω → ℕ → ℝ := fun q g x t =>
        (∑ y in cell q x t, g y) / ((cell q x t).card : ℝ)
      let variance : Strategy → (Ω → ℝ) → Ω → ℕ → ℝ := fun q g x t =>
        (∑ y in cell q x t, (g y - mean q g x t) ^ 2) /
          ((cell q x t).card : ℝ)
      let area : Strategy → (Ω → ℝ) → ℝ := fun q g =>
        (∑ x : Ω, ∑ t : Fin (Fintype.card Ω), variance q g x t) /
          (Fintype.card Ω : ℝ)
      ∃ q : Strategy, Fresh q ∧ area q target ≤ 2

end

end MathlibPlus.Open.Probability
