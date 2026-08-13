import Mathlib

namespace MathlibPlus.Algebra

/-- The displayed unimodal coefficient vectors satisfy the coarse constraints,
while their coefficient convolution has the exhibited strict valley. -/
theorem coarseUnimodalityConstraints_counterexample_claim46731 :
    let A : Fin 16 → ℕ :=
      ![1, 20, 181, 995, 2986, 9949, 14650, 7285,
        6742, 6007, 3005, 1591, 1278, 1273, 140, 131]
    let B : Fin 19 → ℕ :=
      ![1, 27, 333, 2543, 16174, 19985, 201036, 57263,
        52483, 52459, 46057, 33196, 29740, 13321, 9030, 1377,
        981, 964, 684]
    let unimodal : ∀ {n : ℕ}, (Fin n → ℕ) → Prop := fun {n} v =>
      ∃ p : Fin n,
        (∀ i j : Fin n, i ≤ j → j ≤ p → v i ≤ v j) ∧
        (∀ i j : Fin n, p ≤ i → i ≤ j → v j ≤ v i)
    let conv : (Fin 16 → ℕ) → (Fin 19 → ℕ) → ℕ → ℕ := fun A B k =>
      ∑ i : Fin 16, if h : i.val ≤ k ∧ k - i.val < 19 then
        A i * B ⟨k - i.val, h.2⟩
      else 0
    unimodal A ∧ unimodal B ∧
      A 1 = 20 ∧ A 2 = Nat.choose 20 2 - (20 - 11) ∧
      15 ≥ (20 + 1) / 2 ∧
      (∀ k : Fin 16, A k ≥ Nat.choose 15 k) ∧
      B 1 = 27 ∧ B 2 = Nat.choose 27 2 - (27 - 9) ∧
      18 ≥ (27 + 1) / 2 ∧
      (∀ k : Fin 19, B k ≥ Nat.choose 18 k) ∧
      conv A B 12 = 4003784441 ∧
      conv A B 13 = 3274792848 ∧
      conv A B 14 = 3412709583 ∧
      conv A B 12 > conv A B 13 ∧ conv A B 13 < conv A B 14 := by
  native_decide

end MathlibPlus.Algebra
