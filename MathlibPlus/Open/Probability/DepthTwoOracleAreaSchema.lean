import Mathlib

namespace MathlibPlus.Open.Probability.DepthTwoOracleAreaSchema

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev Strategy (n : ℕ) := List Bool → Fin n

def transcript {n : ℕ} (q : Strategy n) (x : Cube n) : ℕ → List Bool :=
  fun m => Nat.rec [] (fun _ answers => answers ++ [x (q answers)]) m

def Fresh {n : ℕ} (q : Strategy n) : Prop :=
  ∀ (x : Cube n) (a b : ℕ), a < b → b < n →
    q (transcript q x a) ≠ q (transcript q x b)

def DepthAtMostTwo {n : ℕ} (h : Cube n → Bool) : Prop :=
  ∃ (q : Strategy n) (done out : List Bool → Bool),
    Fresh q ∧
    (∀ x : Cube n, ∃ m : ℕ, m ≤ 2 ∧ done (transcript q x m) = true) ∧
    ∀ (x : Cube n) (m : ℕ), m ≤ 2 → done (transcript q x m) = true →
      h x = out (transcript q x m)

noncomputable def conditionalVariance {n : ℕ}
    (g : Cube n → ℝ) (q : Strategy n) (x : Cube n) (m : ℕ) : ℝ := by
  classical
  let cell := Finset.filter
    (fun y : Cube n => transcript q y m = transcript q x m)
    (Finset.univ : Finset (Cube n))
  let card : ℝ := cell.card
  let mean := (∑ y ∈ cell, g y) / card
  exact (∑ y ∈ cell, (g y) ^ 2) / card - mean ^ 2

noncomputable def policyArea {n : ℕ} (g : Cube n → ℝ) (q : Strategy n) : ℝ :=
  ∑ m ∈ Finset.range n,
    (∑ x : Cube n, conditionalVariance g q x m) / (2 : ℝ) ^ n

def signReal (b : Bool) : ℝ := if b then 1 else -1

def mixture {m n : ℕ} (h : Fin m → Cube n → Bool)
    (weight : Fin m → ℝ) : Cube n → ℝ :=
  fun x => ∑ i, weight i * signReal (h i x)

def mixtureAreaAtMost (m n : ℕ) : Prop :=
  ∀ (h : Fin m → Cube n → Bool) (weight : Fin m → ℝ),
    (∀ i, 0 ≤ weight i) →
    (∑ i, weight i) = 1 →
    (∀ i, DepthAtMostTwo (h i)) →
    ∃ q : Strategy n, Fresh q ∧ policyArea (mixture h weight) q ≤ 2

def heavyMixtureAreaAtMost (m n : ℕ) (threshold : ℝ) : Prop :=
  ∀ (h : Fin m → Cube n → Bool) (weight : Fin m → ℝ),
    (∀ i, 0 ≤ weight i) →
    (∑ i, weight i) = 1 →
    (∃ j : Fin m, threshold ≤ weight j) →
    (∀ i, DepthAtMostTwo (h i)) →
    ∃ q : Strategy n, Fresh q ∧ policyArea (mixture h weight) q ≤ 2

def OptimalFor {n : ℕ} (g : Cube n → ℝ) (q : Strategy n) : Prop :=
  Fresh q ∧ ∀ r : Strategy n, Fresh r → policyArea g q ≤ policyArea g r

def twoComponentIntrinsicAreaChord (n : ℕ) : Prop :=
  ∀ (h k : Cube n → Bool) (t : ℝ),
    DepthAtMostTwo h → DepthAtMostTwo k →
    0 ≤ t → t ≤ 1 →
    ∃ (qh qk q : Strategy n),
      OptimalFor (fun x => signReal (h x)) qh ∧
      OptimalFor (fun x => signReal (k x)) qk ∧
      Fresh q ∧
      policyArea
          (fun x => (1 - t) * signReal (h x) + t * signReal (k x)) q ≤
        (1 - t) * policyArea (fun x => signReal (h x)) qh +
          t * policyArea (fun x => signReal (k x)) qk


def radialBooleanAreaAtMost (n : ℕ) : Prop :=
  ∀ (u : Cube n → Bool) (α : ℝ),
    (∃ (m : ℕ) (h : Fin m → Cube n → Bool) (weight : Fin m → ℝ),
      (∀ i, 0 ≤ weight i) ∧
      (∑ i, weight i) = 1 ∧
      (∀ i, DepthAtMostTwo (h i)) ∧
      ∀ x, α * signReal (u x) = mixture h weight x) →
    ∃ q : Strategy n, Fresh q ∧
      policyArea (fun x => α * signReal (u x)) q ≤ 2

end

end MathlibPlus.Open.Probability.DepthTwoOracleAreaSchema
