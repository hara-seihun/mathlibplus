import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- All failures of simultaneous directed Cayley CI on the cyclic group of order
eight are affine copies of one exceptional rooted permutation, and occur exactly
when the relation family distinguishes both exceptional atom pairs. -/
def cyclicEightDirectedRelationalDefectClassification : Prop :=
  let q₀ : ZMod 8 → ZMod 8 := fun x =>
    if x = 2 then 6 else if x = 6 then 2 else
    if x = 3 then 7 else if x = 7 then 3 else x
  ∀ (ι : Type) (S T : ι → Set (ZMod 8)) (e : ZMod 8 ≃ ZMod 8),
    (∀ i, 0 ∉ S i) →
    (∀ i, 0 ∉ T i) →
    (∀ i x y, y - x ∈ S i ↔ e y - e x ∈ T i) →
    (¬ ∃ φ : ZMod 8 ≃+ ZMod 8, ∀ i x, x ∈ S i ↔ φ x ∈ T i) ↔
      (∃ (α β : ZMod 8 ≃+ ZMod 8) (a : ZMod 8),
        ∀ x, e x - e 0 = β (q₀ (α x + a) - q₀ a)) ∧
      (∃ i, ¬ (1 ∈ S i ↔ 3 ∈ S i)) ∧
      (∃ i, ¬ (2 ∈ S i ↔ 6 ∈ S i))

end MathlibPlus.Open.GraphTheory
