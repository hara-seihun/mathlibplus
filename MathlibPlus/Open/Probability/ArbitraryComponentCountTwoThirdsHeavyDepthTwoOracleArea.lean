import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
For every positive finite number of displayed components, a convex mixture of
Boolean functions computed by deterministic decision trees of worst-case depth
at most two on a finite uniform Boolean cube has an adaptive fresh-coordinate
policy of root-inclusive cumulative posterior-variance area at most two when
one displayed component has weight at least `2 / 3`. Zero weights and repeated
semantic functions are allowed; the zero-dimensional cube is discharged by a
separate trivial disjunct.
-/
def arbitraryComponentCountTwoThirdsHeavyDepthTwoOracleArea : Prop :=
  ∀ m : ℕ, 0 < m →
    ∀ n : ℕ, n = 0 ∨
      let Ω := Fin n → Bool
      let Strategy := List Bool → Fin n
      let transcript : Strategy → Ω → ℕ → List Bool := fun q x t =>
        Nat.rec [] (fun _ answers => answers ++ [x (q answers)]) t
      let Fresh : Strategy → Prop := fun q =>
        ∀ (x : Ω) (a b : ℕ), a < b → b < n →
          q (transcript q x a) ≠ q (transcript q x b)
      let DepthAtMostTwo : (Ω → Bool) → Prop := fun h =>
        ∃ (q : Strategy) (done out : List Bool → Bool),
          Fresh q ∧
          (∀ x : Ω, ∃ t : ℕ, t ≤ 2 ∧
            done (transcript q x t) = true) ∧
          ∀ (x : Ω) (t : ℕ), t ≤ 2 →
            done (transcript q x t) = true →
            h x = out (transcript q x t)
      let conditionalVariance : (Ω → ℝ) → Strategy → Ω → ℕ → ℝ :=
        fun g q x t => by
          classical
          let cell := Finset.filter
            (fun y : Ω => transcript q y t = transcript q x t)
            (Finset.univ : Finset Ω)
          let card : ℝ := cell.card
          let mean := (∑ y ∈ cell, g y) / card
          exact (∑ y ∈ cell, (g y) ^ 2) / card - mean ^ 2
      let PolicyArea : (Ω → ℝ) → Strategy → ℝ := fun g q =>
        ∑ t ∈ Finset.range n,
          (∑ x : Ω, conditionalVariance g q x t) / (2 : ℝ) ^ n
      let sgn : Bool → ℝ := fun b => if b then 1 else -1
      ∀ (h : Fin m → Ω → Bool) (weight : Fin m → ℝ),
        (∀ i, 0 ≤ weight i) →
        (∑ i, weight i) = 1 →
        (∃ j : Fin m, (2 : ℝ) / 3 ≤ weight j) →
        (∀ i, DepthAtMostTwo (h i)) →
        ∃ q : Strategy, Fresh q ∧
          PolicyArea (fun x => ∑ i, weight i * sgn (h i x)) q ≤ 2

end

end MathlibPlus.Open.Probability
