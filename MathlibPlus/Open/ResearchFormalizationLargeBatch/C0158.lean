import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim2464_exactFirstCellArithmeticMap : Prop := by
  classical
  exact ∀ (B c δ : ℝ) (φ : ℝ → ℝ),
    1 < B → B < 2 → c > B →
    ContDiff ℝ ⊤ φ → Function.support φ ⊆ Set.Ioo 1 B →
    let p : ℝ → ℝ := fun v => δ * Real.sqrt c * φ (c * |v|)
    let kφ : ℝ → ℝ := fun x => Real.exp (x / 2) * φ (Real.exp x)
    let K : ℝ → ℝ := fun x =>
      Real.exp (x / 2) / Real.sqrt c *
        ∑ n ∈ Finset.Icc 1 (Nat.ceil (c * Real.exp (-x))),
          if (1 : ℝ) ≤ n ∧ (n : ℝ) < c * Real.exp (-x) then
            p ((n : ℝ) * Real.exp x / c)
          else 0
    (∀ x, 0 < x ∧ x < Real.log B → K x = δ * kφ x) ∧
      (∀ x, Real.log B ≤ x ∧ x ≤ Real.log c → K x = 0)

def claim2466_exactPacketL2Norm : Prop := by
  exact ∀ (B c δ : ℝ) (φ : ℝ → ℝ),
    1 < B → B < 2 → c > B →
    ContDiff ℝ ⊤ φ → Function.support φ ⊆ Set.Ioo 1 B →
    let p : ℝ → ℝ := fun v => δ * Real.sqrt c * φ (c * |v|)
    let kφ : ℝ → ℝ := fun x => Real.exp (x / 2) * φ (Real.exp x)
    (∫ v : ℝ, |p v| ^ 2) =
      2 * δ ^ 2 * (∫ x in (0 : ℝ)..Real.log B, |kφ x| ^ 2)

def claim2468_closedSubstripTransformBound : Prop := by
  exact ∀ (B c δ Y : ℝ) (φ : ℝ → ℝ) (z : ℂ),
    1 < B → B < 2 → c > B →
    ContDiff ℝ ⊤ φ → Function.support φ ⊆ Set.Ioo 1 B →
    0 ≤ Y → |z.im| ≤ Y →
    let kφ : ℝ → ℝ := fun x => Real.exp (x / 2) * φ (Real.exp x)
    let G : ℂ → ℂ := fun w =>
      (δ : ℂ) * ∫ x in (0 : ℝ)..Real.log B,
        (kφ x : ℂ) * Complex.cos (w * ((x - Real.log c / 2 : ℝ) : ℂ))
    ‖G z‖ ≤ |δ| * c ^ (Y / 2) * ∫ x in (0 : ℝ)..Real.log B, |kφ x|

end MathlibPlus.Open.ResearchFormalizationLargeBatch
