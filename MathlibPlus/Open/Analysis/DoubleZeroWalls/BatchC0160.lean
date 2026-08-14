import Mathlib

namespace MathlibPlus.Open.Analysis.DoubleZeroWalls

noncomputable section

/-- Claim 2486: the quadratic normal form at a nondegenerate double-zero wall,
including the uniform two-variable remainder estimate and its restriction to
nearby zeroes. -/
def quadraticNormalFormAtNondegenerateDoubleWall_claim2486 : Prop :=
  ∀ (F₀ C : ℝ → ℝ) (x s : ℝ),
    ContDiffAt ℝ 2 F₀ x →
    ContDiffAt ℝ 2 C x →
    F₀ x + s * C x = 0 →
    deriv (fun y : ℝ => F₀ y + s * C y) x = 0 →
    let H := deriv (deriv F₀) x + s * deriv (deriv C) x
    H ≠ 0 →
      (∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          (∀ s' z : ℝ,
            |s' - s| < δ → |z - x| < δ →
            |(F₀ z + s' * C z) -
                (C x * (s' - s) + H / 2 * (z - x) ^ 2)| ≤
              ε * (|s' - s| + |z - x| ^ 2)) ∧
          (∀ s' z : ℝ,
            |s' - s| < δ → |z - x| < δ →
            F₀ z + s' * C z = 0 →
            |(z - x) ^ 2 + (2 * C x / H) * (s' - s)| ≤
              ε * |s' - s|))

/-- Claim 2490: at a simple upper-edge zero, the imaginary velocity of the
implicit zero branch gives exit, entry, or tangency as the parameter rises. -/
def upperEdgeEntryExitOrientation_claim2490 : Prop :=
  ∀ (F₀ C : ℂ → ℂ) (s : ℝ) (z : ℂ) (Y : ℝ),
    z.im = Y →
    F₀ z + (s : ℂ) * C z = 0 →
    deriv F₀ z + (s : ℂ) * deriv C z ≠ 0 →
    let v := -C z / (deriv F₀ z + (s : ℂ) * deriv C z)
    (∀ γ : ℝ → ℂ,
      γ s = z →
      (∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, |t - s| < δ → F₀ (γ t) + (t : ℂ) * C (γ t) = 0) →
      HasDerivAt γ v s →
      ((0 < v.im →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, s < t → t < s + δ → Y < (γ t).im) ∧
        (v.im < 0 →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t : ℝ, s < t → t < s + δ → (γ t).im < Y) ∧
        (v.im = 0 →
          Complex.im (deriv γ s) = 0)))

end

end MathlibPlus.Open.Analysis.DoubleZeroWalls
