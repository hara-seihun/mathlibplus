import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5752UnimodalConvolution

noncomputable section

/-- Claim 56923: two explicit nonnegative unimodal finite sequences can have a
non-unimodal convolution. -/
def unimodalConvolutionCounterexample_claim56923 : Prop :=
  let a : ℕ → ℕ := fun i =>
    if i = 0 then 1 else if i = 1 then 7 else if i = 2 then 2 else
      if i = 3 then 2 else if i = 4 then 1 else 0
  let b : ℕ → ℕ := fun i =>
    if i = 0 then 1 else if i = 1 then 8 else if i = 2 then 5 else
      if i = 3 then 5 else if i = 4 then 2 else if i = 5 then 2 else
        if i = 6 then 1 else 0
  let unimodal : ∀ n : ℕ, (Fin n → ℕ) → Prop := fun n u =>
    ∃ p : Fin n,
      (∀ i j : Fin n, i ≤ j → j ≤ p → u i ≤ u j) ∧
        (∀ i j : Fin n, p ≤ i → i ≤ j → u j ≤ u i)
  let af : Fin 5 → ℕ := fun i => a i
  let bf : Fin 7 → ℕ := fun i => b i
  let convolution : Fin 11 → ℕ := fun k =>
    (Finset.range (k.val + 1)).sum (fun i => a i * b (k.val - i))
  let target : Fin 11 → ℕ :=
    ![1, 15, 63, 58, 64, 44, 34, 20, 8, 4, 1]
  unimodal 5 af ∧
    unimodal 7 bf ∧
    (∀ k : Fin 11, convolution k = target k) ∧
    convolution 2 = 63 ∧ convolution 3 = 58 ∧ convolution 4 = 64 ∧
    convolution 2 > convolution 3 ∧ convolution 3 < convolution 4 ∧
    ¬ unimodal 11 convolution

end

end MathlibPlus.Open.ResearchFormalization.R5752UnimodalConvolution
