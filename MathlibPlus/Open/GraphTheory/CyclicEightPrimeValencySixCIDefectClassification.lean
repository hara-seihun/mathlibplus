import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- For every odd prime `p`, all valency-six undirected Cayley CI defects on
`C_p × C_8` are the two-parameter orientation-tag family coming from the
classical directed defect on `C_8`. -/
def cyclicEightPrimeValencySixCIDefectClassification : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    let X : ZMod p → ZMod p → Set (ZMod p × ZMod 8) := fun r s =>
      {x | (x.1 = r ∧ (x.2 = 1 ∨ x.2 = 5)) ∨
           (x.1 = -r ∧ (x.2 = 3 ∨ x.2 = 7)) ∨
           x = (s, 2) ∨ x = (-s, 6)}
    let Y : ZMod p → ZMod p → Set (ZMod p × ZMod 8) := fun r s =>
      {x | (x.1 = r ∧ (x.2 = 1 ∨ x.2 = 5)) ∨
           (x.1 = -r ∧ (x.2 = 3 ∨ x.2 = 7)) ∨
           x = (s, 6) ∨ x = (-s, 2)}
    ∀ (S T : Set (ZMod p × ZMod 8))
      (e : (ZMod p × ZMod 8) ≃ (ZMod p × ZMod 8)),
      (0, 0) ∉ S → (0, 0) ∉ T →
      (∀ x, -x ∈ S ↔ x ∈ S) →
      (∀ x, -x ∈ T ↔ x ∈ T) →
      S.ncard = 6 → T.ncard = 6 →
      (∀ x y, y - x ∈ S ↔ e y - e x ∈ T) →
      (¬ ∃ φ : (ZMod p × ZMod 8) ≃+ (ZMod p × ZMod 8),
          ∀ x, x ∈ S ↔ φ x ∈ T) ↔
        ∃ (r s : ZMod p)
          (α β : (ZMod p × ZMod 8) ≃+ (ZMod p × ZMod 8)),
          r ≠ 0 ∧ s ≠ 0 ∧
          (((∀ x, x ∈ S ↔ α x ∈ X r s) ∧
            (∀ x, x ∈ T ↔ β x ∈ Y r s)) ∨
           ((∀ x, x ∈ S ↔ α x ∈ Y r s) ∧
            (∀ x, x ∈ T ↔ β x ∈ X r s)))

end MathlibPlus.Open.GraphTheory
