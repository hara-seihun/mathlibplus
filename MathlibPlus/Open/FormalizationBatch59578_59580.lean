import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

/-- Claim 59578: uniform profile transfer for the interior-edge law. -/
def admittedClaim59578 : Prop :=
  ∀ (L : ℕ → ℝ) (m : ℕ → ℕ → ℝ),
    (∀ n, 0 < n → 0 < L n) →
    (∀ n j, j < n → 0 ≤ m n j) →
    let a : ℕ → ℝ := fun n => (Finset.range n).sum (fun j => m n j)
    let pi : ℕ → ℕ → ℝ := fun n j =>
      if 0 < a n then m n j / a n else 0
    let delta : ℕ → ℝ := fun n =>
      if h : 0 < n then
        (Finset.range n).sup' (by
          refine ⟨0, ?_⟩
          exact Finset.mem_range.mpr h) (fun j =>
          |16 * (n : ℝ) ^ 2 * (1 + (j : ℝ) / (n : ℝ)) ^ 2 *
              m n j / L n - 1|)
      else 0
    Filter.Tendsto delta Filter.atTop (nhds 0) →
      (Asymptotics.IsEquivalent Filter.atTop a (fun n => L n / (32 * (n : ℝ)))) ∧
        (Asymptotics.IsEquivalent Filter.atTop
          (fun n => (Finset.range n).sum (fun j => (pi n j) ^ 2))
          (fun n => (7 : ℝ) / (6 * (n : ℝ))))

/-- Claim 59580: full-support proportional transport. -/
def admittedClaim59580 : Prop :=
  ∀ (N P : Type*) [Fintype N] [Fintype P]
    (a : N → ℝ) (b : P → ℝ),
    (∀ j, 0 ≤ b j) →
    0 < Finset.univ.sum b →
    (Finset.univ.sum a) < Finset.univ.sum b →
    let B : ℝ := Finset.univ.sum b
    let T : N → P → ℝ := fun _ j => b j / B
    (∀ i, Finset.univ.sum (fun j => T i j) = 1) ∧
      (∀ i j, 0 ≤ T i j) ∧
        (∀ j, (Finset.univ.sum (fun i => T i j * a i)) ≤ b j) ∧
          (∀ j, 0 < b j → (Finset.univ.sum (fun i => T i j * a i)) < b j)

end MathlibPlus.Open
