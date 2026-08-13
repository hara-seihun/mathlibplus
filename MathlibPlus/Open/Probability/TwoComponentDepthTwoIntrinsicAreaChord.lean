import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
On every finite uniform Boolean cube, intrinsic cumulative posterior-variance
area is chord-convex between any two Boolean functions of deterministic
decision-tree depth at most two.
-/
def twoComponentDepthTwoIntrinsicAreaChord : Prop :=
  ∀ n : ℕ, n = 0 ∨
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
    let OptimalFor : (Ω → ℝ) → Strategy → Prop := fun g q =>
      Fresh q ∧ ∀ r : Strategy, Fresh r → PolicyArea g q ≤ PolicyArea g r
    let sgn : Bool → ℝ := fun b => if b then 1 else -1
    ∀ (h k : Ω → Bool) (t : ℝ),
      DepthAtMostTwo h → DepthAtMostTwo k →
      0 ≤ t → t ≤ 1 →
      ∃ (qh qk q : Strategy),
        OptimalFor (fun x => sgn (h x)) qh ∧
        OptimalFor (fun x => sgn (k x)) qk ∧
        Fresh q ∧
        PolicyArea
            (fun x => (1 - t) * sgn (h x) + t * sgn (k x)) q ≤
          (1 - t) * PolicyArea (fun x => sgn (h x)) qh +
            t * PolicyArea (fun x => sgn (k x)) qk

end

end MathlibPlus.Open.Probability
