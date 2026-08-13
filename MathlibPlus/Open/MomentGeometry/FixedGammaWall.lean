import Mathlib

open scoped BigOperators

/-!
# Fixed-gamma completed-Bezout wall

Statement-fidelity formalization of admitted claim 7509. The source's phrase
"strict generalized Stieltjes moment total positivity" is made inspectable as
strict positivity of every finite ordered minor of every shifted Hankel matrix
of the gamma moments `(α)_n`. The completed Bezout matrix is inlined from the
source formula; no pivot-only surrogate is used for the final chamber claim.
-/

namespace MathlibPlus.Open.MomentGeometry

/-- Every fixed positive gamma shape has strict generalized moment TP, while
its completed-Bezout chamber eventually encounters a negative pivot and hence
is not positive definite at every rank. -/
def fixedGammaLawLeavesPositiveChamber_claim7509 : Prop :=
  ∀ α : ℝ, 0 < α →
    let moment : ℕ → ℝ := fun n ↦
      ∏ k ∈ Finset.range n, (α + (k : ℝ))
    let h : ℕ → ℝ := fun n ↦
      moment n / (Nat.factorial (2 * n) : ℝ)
    let completedBezout : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ := fun _ i j ↦
      ∑ a ∈ Finset.range (min i.val j.val + 1),
        ((i.val + j.val + 1 - 2 * a : ℕ) : ℝ) *
          h a * h (i.val + j.val + 1 - a)
    (∀ (r s : ℕ) (rows cols : Fin r ↪o ℕ),
        0 < Matrix.det (fun i j : Fin r ↦
          moment (s + (rows i : ℕ) + (cols j : ℕ)))) ∧
      (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        2 * α - (2 * (N : ℝ) - 3) < 0) ∧
      ¬(∀ N : ℕ, 1 ≤ N → Matrix.PosDef (completedBezout N))

end MathlibPlus.Open.MomentGeometry

namespace MathlibPlus.MomentGeometry

/-- The arithmetic wall in claim 7509 is eventually negative, independently
of the unresolved generalized-total-positivity part of the claim. -/
theorem fixedGammaPivot_eventually_negative_claim7509
    (α : ℝ) (_hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 * α - (2 * (N : ℝ) - 3) < 0 := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (α + (3 / 2 : ℝ))
  refine ⟨N₀, ?_⟩
  intro N hN
  have hNcast : (N₀ : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hgt : α + (3 / 2 : ℝ) < (N : ℝ) :=
    lt_of_lt_of_le hN₀ hNcast
  linarith

end MathlibPlus.MomentGeometry
