import Mathlib

namespace MathlibPlus.Open.Probability.CommonLeaf

noncomputable section

/-- The full-depth common-leaf family: private gate coordinates are queried
first, and the terminal coordinate is private except on the all-`true` gate
word, where it is shared by every component. -/
def claim48476_fullDepthCommonLeafConstruction : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → 2 ≤ k →
    let GateWord := Fin (k - 1) → Bool
    let allPlus : GateWord → Prop := fun w => ∀ j, w j = true
    let PrivateWord := {w : GateWord // ¬ allPlus w}
    let Coord :=
      (Fin n × Fin (k - 1)) ⊕ ((Fin n × PrivateWord) ⊕ Unit)
    let Ω := Coord → Bool
    let gateWord : Fin n → Ω → GateWord := fun i x j =>
      x (Sum.inl (i, j))
    let leaf : Fin n → Ω → Coord := fun i x =>
      if h : allPlus (gateWord i x) then
        Sum.inr (Sum.inr ())
      else
        Sum.inr (Sum.inl (i, ⟨gateWord i x, h⟩))
    let path : Fin n → Ω → List Coord := fun i x =>
      List.ofFn (fun j : Fin (k - 1) => (Sum.inl (i, j) : Coord)) ++ [leaf i x]
    let output : Fin n → Ω → Bool := fun i x => x (leaf i x)
    (∀ i x, (path i x).length = k ∧ (path i x).Nodup) ∧
      (∀ i j, ∃ x y : Ω,
        x (Sum.inl (i, j)) ≠ y (Sum.inl (i, j)) ∧
          (∀ c, c ≠ Sum.inl (i, j) → x c = y c) ∧
          output i x ≠ output i y) ∧
      (∀ i (w : PrivateWord), ∃ x y : Ω,
        x (Sum.inr (Sum.inl (i, w))) ≠
            y (Sum.inr (Sum.inl (i, w))) ∧
          (∀ c, c ≠ Sum.inr (Sum.inl (i, w)) → x c = y c) ∧
          output i x ≠ output i y) ∧
      (∀ i, ∃ x y : Ω,
        x (Sum.inr (Sum.inr ())) ≠ y (Sum.inr (Sum.inr ())) ∧
          (∀ c, c ≠ Sum.inr (Sum.inr ()) → x c = y c) ∧
          output i x ≠ output i y)

end

end MathlibPlus.Open.Probability.CommonLeaf
