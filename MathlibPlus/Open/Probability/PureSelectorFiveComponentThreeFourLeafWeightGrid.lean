-- UNVERIFIED (does-not-elaborate): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Open.Probability

noncomputable section

/--
On the finite denominator grid of five pure two-level selector components
with three or four shared leaves and total weight at most twenty, the exact
optimal root-inclusive posterior-variance area has maximum `671 / 400`.
-/
def pureSelectorFiveComponentThreeFourLeafWeightGrid : Prop :=
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
        Option.map y ((run q x n)[j.val]?) =
          Option.map x ((run q x n)[j.val]?)
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
  let selector : ∀ {p : ℕ}, (Fin 5 → Fin p) → (Fin 5 → Fin p) →
      Fin 5 → (Fin 5 ⊕ Fin p → Bool) → ℚ :=
    fun {p} u v e x =>
      if x (Sum.inl e) then sgn (x (Sum.inr (v e)))
      else sgn (x (Sum.inr (u e)))
  let target : ∀ {p : ℕ}, (Fin 5 → Fin p) → (Fin 5 → Fin p) →
      (Fin 5 → ℕ) → ℕ → (Fin 5 ⊕ Fin p → Bool) → ℚ :=
    fun {p} u v w W x =>
      (∑ e : Fin 5, (w e : ℚ) * selector u v e x) / (W : ℚ)
  let baseU : Fin 5 → Fin 3 := fun _ => 0
  let baseV : Fin 5 → Fin 3 := fun _ => 1
  let baseW : Fin 5 → ℕ := fun e => if e.val = 0 then 16 else 1
  (∀ (p W : ℕ),
      3 ≤ p → p ≤ 4 → 5 ≤ W → W ≤ 20 →
      ∀ (u v : Fin 5 → Fin p) (w : Fin 5 → ℕ),
        (∀ e, u e ≠ v e) →
        (∀ e, 1 ≤ w e) →
        (∑ e : Fin 5, w e) = W →
        ∃ q : List Bool → Fin (5 + p),
          legal q ∧ policyArea (target u v w W) q ≤ (671 : ℚ) / 400) ∧
    (∀ q : List Bool → Fin (5 + 3),
      legal q →
      (671 : ℚ) / 400 ≤
        policyArea (target baseU baseV baseW 20) q)

end

end MathlibPlus.Open.Probability
