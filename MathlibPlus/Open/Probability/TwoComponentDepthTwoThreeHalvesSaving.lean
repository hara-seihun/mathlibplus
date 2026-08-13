import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
For a convex mixture of two Boolean functions of deterministic decision-tree
worst-case depth at most two, the target variance is at most three halves times
the largest mixture-average one-coordinate saving in minimum expected query
cost.  The constant `3/2` is sharp.
-/
def twoComponentDepthTwoThreeHalvesSaving : Prop :=
  ∀ n : ℕ, n = 0 ∨
    let Ω := Fin n → Bool
    let Strategy := List Bool → Fin n
    let transcript : Strategy → Ω → ℕ → List Bool := fun q x m =>
      Nat.rec [] (fun _ answers => answers ++ [x (q answers)]) m
    let Fresh : Strategy → Prop := fun q =>
      ∀ (x : Ω) (a b : ℕ), a < b → b < n →
        q (transcript q x a) ≠ q (transcript q x b)
    let TreeCert : (Ω → Bool) → Strategy → (List Bool → Bool) →
        (List Bool → Bool) → (Ω → ℕ) → Prop := fun h q done out stop =>
      Fresh q ∧
      (∀ x, stop x ≤ n) ∧
      (∀ x, done (transcript q x (stop x)) = true) ∧
      (∀ x m, m < stop x → done (transcript q x m) = false) ∧
      (∀ x, h x = out (transcript q x (stop x)))
    let qCost : (Ω → Bool) → ℝ := fun h =>
      sInf {c : ℝ | ∃ (q : Strategy) (done out : List Bool → Bool)
          (stop : Ω → ℕ),
        TreeCert h q done out stop ∧
        c = (∑ x : Ω, (stop x : ℝ)) / (2 : ℝ) ^ n}
    let DepthAtMostTwo : (Ω → Bool) → Prop := fun h =>
      ∃ (q : Strategy) (done out : List Bool → Bool) (stop : Ω → ℕ),
        TreeCert h q done out stop ∧ ∀ x, stop x ≤ 2
    let restrict : (Ω → Bool) → Fin n → Bool → Ω → Bool := fun h i b x =>
      h (Function.update x i b)
    let saving : (Ω → Bool) → Fin n → ℝ := fun h i =>
      qCost h - (qCost (restrict h i false) + qCost (restrict h i true)) / 2
    let sgn : Bool → ℝ := fun b => if b then 1 else -1
    let uniformVariance : (Ω → ℝ) → ℝ := fun g =>
      let mean := (∑ x : Ω, g x) / (2 : ℝ) ^ n
      (∑ x : Ω, (g x) ^ 2) / (2 : ℝ) ^ n - mean ^ 2
    ∀ (h k : Ω → Bool) (t : ℝ),
      DepthAtMostTwo h → DepthAtMostTwo k →
      0 ≤ t → t ≤ 1 →
      ∃ i : Fin n,
        uniformVariance (fun x => t * sgn (h x) + (1 - t) * sgn (k x)) ≤
          (3 / 2 : ℝ) * (t * saving h i + (1 - t) * saving k i)

end

end MathlibPlus.Open.Probability
