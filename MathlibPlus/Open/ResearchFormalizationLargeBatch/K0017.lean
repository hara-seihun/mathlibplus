import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim7514_finiteOneHeightPresentationsLoadAndCycleWeight : Prop := by
  classical
  exact ∀ (m : ℕ × ℕ →₀ ℕ),
    m (0, 0) = 0 →
    let ell : ℕ × ℕ → ℕ := fun z => 2 * z.1 + z.2
    let cCount : ℕ → ℕ := fun l => l / 2 + 1
    let load : ℕ := ∑ z ∈ m.support, m z * ell z
    let weight : ℝ :=
      ∏ z ∈ m.support,
        (1 : ℝ) /
          ((m z).factorial *
            (((ell z * cCount (ell z)) ^ (m z) : ℕ) : ℝ))
    load = ∑ z ∈ m.support, m z * (2 * z.1 + z.2) ∧
      weight =
        ∏ z ∈ m.support,
          (1 : ℝ) /
            ((m z).factorial *
              ((((2 * z.1 + z.2) *
                cCount (2 * z.1 + z.2)) ^ (m z) : ℕ) : ℝ))

def claim7517_eulerScarweaveAndSeamInteger : Prop := by
  classical
  exact ∀ (X : ℕ →₀ (ℕ × ℕ →₀ ℕ)),
    (∀ p, X p (0, 0) = 0) →
    (∀ p, X p ≠ 0 → Nat.Prime p) →
    let ell : ℕ × ℕ → ℕ := fun z => 2 * z.1 + z.2
    let cCount : ℕ → ℕ := fun l => l / 2 + 1
    let load : (ℕ × ℕ →₀ ℕ) → ℕ := fun m =>
      ∑ z ∈ m.support, m z * ell z
    let weight : (ℕ × ℕ →₀ ℕ) → ℝ := fun m =>
      ∏ z ∈ m.support,
        (1 : ℝ) /
          ((m z).factorial *
            (((ell z * cCount (ell z)) ^ (m z) : ℕ) : ℝ))
    let a : ℕ → ℕ := fun p => load (X p)
    let N : ℕ := ∏ p ∈ X.support, p ^ a p
    let ω : ℝ := ∏ p ∈ X.support, weight (X p)
    (∀ p, a p = ∑ z ∈ (X p).support, (X p) z * (2 * z.1 + z.2)) ∧
      N = ∏ p ∈ X.support, p ^ a p ∧
      ω = ∏ p ∈ X.support, weight (X p)

def claim7520_zetaGibbsMeasureAndSeamPushforward : Prop := by
  classical
  exact ∀ (σ : ℝ), 1 < σ →
    let Local := ℕ × ℕ →₀ ℕ
    let Family := ℕ →₀ Local
    let Valid : Family → Prop := fun X =>
      (∀ p, X p (0, 0) = 0) ∧ (∀ p, X p ≠ 0 → Nat.Prime p)
    let Ω := {X : Family // Valid X}
    let ell : ℕ × ℕ → ℕ := fun z => 2 * z.1 + z.2
    let cCount : ℕ → ℕ := fun l => l / 2 + 1
    let load : Local → ℕ := fun m =>
      ∑ z ∈ m.support, m z * ell z
    let localWeight : Local → ℝ := fun m =>
      ∏ z ∈ m.support,
        (1 : ℝ) /
          ((m z).factorial *
            (((ell z * cCount (ell z)) ^ (m z) : ℕ) : ℝ))
    let seam : Family → ℕ := fun X =>
      ∏ p ∈ X.support, p ^ load (X p)
    let weight : Family → ℝ := fun X =>
      ∏ p ∈ X.support, localWeight (X p)
    let zetaσ : ℝ := (riemannZeta (σ : ℂ)).re
    let Pσ : Ω → ℝ := fun X =>
      weight X.1 * Real.rpow (seam X.1 : ℝ) (-σ) / zetaσ
    (∀ X, 0 ≤ Pσ X) ∧
      (∑' X : Ω, Pσ X = 1) ∧
      (∀ n : ℕ, 0 < n →
        (∑' X : Ω, if seam X.1 = n then Pσ X else 0) =
          Real.rpow (n : ℝ) (-σ) / zetaσ)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
