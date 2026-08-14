import Mathlib

namespace MathlibPlus.Open.SchwartzMomentObstruction

open scoped BigOperators

/-- A concrete Schwartz bound for sequences indexed by the nonnegative integers. -/
def SchwartzSequence (a : ℕ → ℝ) : Prop :=
  ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ((n + 1 : ℝ) ^ q) * |a n| ≤ C

def absolutelyConvergentMoment (a : ℕ → ℝ) (q : ℕ) : Prop :=
  Summable (fun n : ℕ => |a n| * (n + 1 : ℝ) ^ q)

def claim59575 : Prop :=
  ∃ ρ θ : ℕ → ℝ,
    (∀ n : ℕ, 0 < ρ n) ∧
    SchwartzSequence θ ∧
    SchwartzSequence (fun n => ρ n - 1) ∧
    (∃ n : ℕ, θ n ≠ 0) ∧
    (∀ q : ℕ,
      absolutelyConvergentMoment
        (fun n => Real.sinh ((n + 1 : ℝ) * θ n)) q ∧
      ∑' n : ℕ, Real.sinh ((n + 1 : ℝ) * θ n) * (n + 1 : ℝ) ^ q = 0) ∧
    (∀ n : ℕ,
      Real.log (ρ n) / (n + 1 : ℝ) = θ n)

end MathlibPlus.Open.SchwartzMomentObstruction
