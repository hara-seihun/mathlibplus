import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
On the uniform four-sign cube, every scalar multiple of a Boolean table that
lies in the convex hull of deterministic depth-at-most-two Boolean tables has
a fresh adaptive coordinate policy with root-inclusive cumulative
posterior-variance area at most two.
-/
def radialBooleanFourCubeDepthTwoOracleArea : Prop :=
  let n : ℕ := 4
  let Ω := Fin n → Bool
  let Strategy := List Bool → Fin n
  let transcript : Strategy → Ω → ℕ → List Bool := fun q x m =>
    Nat.rec [] (fun _ answers => answers ++ [x (q answers)]) m
  let Fresh : Strategy → Prop := fun q =>
    ∀ (x : Ω) (a b : ℕ), a < b → b < n →
      q (transcript q x a) ≠ q (transcript q x b)
  let DepthAtMostTwo : (Ω → Bool) → Prop := fun h =>
    ∃ (q : Strategy) (done out : List Bool → Bool),
      Fresh q ∧
      (∀ x : Ω, ∃ m : ℕ, m ≤ 2 ∧ done (transcript q x m) = true) ∧
      ∀ (x : Ω) (m : ℕ), m ≤ 2 → done (transcript q x m) = true →
        h x = out (transcript q x m)
  let conditionalVariance : (Ω → ℝ) → Strategy → Ω → ℕ → ℝ :=
    fun g q x m => by
      classical
      let cell := Finset.filter
        (fun y : Ω => transcript q y m = transcript q x m)
        (Finset.univ : Finset Ω)
      let card : ℝ := cell.card
      let mean := (∑ y ∈ cell, g y) / card
      exact (∑ y ∈ cell, (g y) ^ 2) / card - mean ^ 2
  let PolicyArea : (Ω → ℝ) → Strategy → ℝ := fun g q =>
    ∑ m ∈ Finset.range n,
      (∑ x : Ω, conditionalVariance g q x m) / (2 : ℝ) ^ n
  let sgn : Bool → ℝ := fun b => if b then 1 else -1
  ∀ (u : Ω → Bool) (α : ℝ),
    (∃ (m : ℕ) (h : Fin m → Ω → Bool) (weight : Fin m → ℝ),
      (∀ i, 0 ≤ weight i) ∧
      (∑ i, weight i) = 1 ∧
      (∀ i, DepthAtMostTwo (h i)) ∧
      ∀ x, α * sgn (u x) = ∑ i, weight i * sgn (h i x)) →
    ∃ q : Strategy, Fresh q ∧
      PolicyArea (fun x => α * sgn (u x)) q ≤ 2

end

end MathlibPlus.Open.Probability
