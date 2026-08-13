import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
On the finite denominator grid of positive pure two-level selector mixtures
with two through four components, two through four shared leaves, and total
weight at most eight, the exact optimal root-inclusive posterior-variance
area has maximum `461 / 256`.
-/
def pureSelectorGraphDepthTwoFiniteGridAreaMaximum : Prop :=
  let sgn : Bool → ℚ := fun b => if b then 1 else -1
  let run : ∀ {n : ℕ}, (List Bool → Fin n) → (Fin n → Bool) →
      ℕ → List (Fin n) :=
    fun {n} q x k =>
      (List.range k).foldl
        (fun h _ => let z := q (h.map x); h ++ [z]) []
  let legal : ∀ {n : ℕ}, (List Bool → Fin n) → Prop :=
    fun {n} q => ∀ x : Fin n → Bool, (run q x n).Nodup
  let samePrefix : ∀ {n : ℕ}, (List Bool → Fin n) →
      (Fin n → Bool) → (Fin n → Bool) → Fin n → Prop :=
    fun {n} q x y t =>
      ∀ j : Fin t.val,
        Option.map y ((run q x n).get? j.val) =
          Option.map x ((run q x n).get? j.val)
  let policyArea : ∀ {n : ℕ}, ((Fin n → Bool) → ℚ) →
      (List Bool → Fin n) → ℚ :=
    fun {n} g q =>
      (∑ x : Fin n → Bool, ∑ t : Fin n,
        let d := (2 : ℚ) ^ (n - t.val)
        let mean :=
          (∑ y : Fin n → Bool,
            if samePrefix q x y t then g y else 0) / d
        (∑ y : Fin n → Bool,
          if samePrefix q x y t then (g y) ^ 2 else 0) / d - mean ^ 2) /
        (2 : ℚ) ^ n
  let selector : ∀ {m p : ℕ}, (Fin m → Fin p) → (Fin m → Fin p) →
      Fin m → (Fin m ⊕ Fin p → Bool) → ℚ :=
    fun {m p} u v e x =>
      if x (Sum.inl e) then sgn (x (Sum.inr (v e)))
      else sgn (x (Sum.inr (u e)))
  let target : ∀ {m p : ℕ}, (Fin m → Fin p) → (Fin m → Fin p) →
      (Fin m → ℕ) → ℕ → (Fin m ⊕ Fin p → Bool) → ℚ :=
    fun {m p} u v w W x =>
      (∑ e : Fin m, (w e : ℚ) * selector u v e x) / (W : ℚ)
  let baseU : Fin 2 → Fin 2 := fun _ => 0
  let baseV : Fin 2 → Fin 2 := fun _ => 1
  let baseW : Fin 2 → ℕ := fun e => if e.val = 0 then 1 else 7
  (∀ (m p W : ℕ),
      2 ≤ m → m ≤ 4 → 2 ≤ p → p ≤ 4 → m ≤ W → W ≤ 8 →
      ∀ (u v : Fin m → Fin p) (w : Fin m → ℕ),
        (∀ e, u e ≠ v e) →
        (∀ e, 1 ≤ w e) →
        (∑ e : Fin m, w e) = W →
        ∃ q : List Bool → Fin (m + p),
          legal q ∧ policyArea (target u v w W) q ≤ (461 : ℚ) / 256) ∧
    (∀ q : List Bool → Fin (2 + 2),
      legal q →
      (461 : ℚ) / 256 ≤
        policyArea (target baseU baseV baseW 8) q)

end

end MathlibPlus.Open.Probability
