import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Probability

/-- Claim 49836: driver-first policies for at most three signed literals have
no positive base Bernstein coefficient and hence no hostile exchangeable
triple tensor. -/
def claim49836_signedLiteralNoHostility : Prop :=
  ∀ s : ℕ, s ≤ 3 →
    let Literal := (Fin s → Bool) → ℚ
    let literal : (Fin s → Bool) → Fin s → Literal := fun ε i x =>
      if x i = ε i then 1 else -1
    let position : (Fin s → Fin s) → Fin s → ℕ := fun p i =>
      (Finset.univ.filter (fun k : Fin s =>
        ∃ l : Fin s, p l = i ∧ k.1 < l.1)).card
    let base : (Fin s → Fin s → Fin s) → Fin s → Fin s → Fin s → ℚ :=
      fun policies i j k =>
        if i = j ∧ j = k then 0
        else if i = j then
          ((position (policies k) i : ℚ) - 3) / 3
        else if i = k then
          ((position (policies j) i : ℚ) - 3) / 3
        else if j = k then
          ((position (policies i) j : ℚ) - 3) / 3
        else -1
    ∀ ε : Fin s → Bool,
      (∀ i : Fin s, ∀ x : Fin s → Bool,
        literal ε i x = if x i = ε i then 1 else -1) ∧
      ∀ policies : Fin s → Fin s → Fin s,
        (∀ j : Fin s, Function.Bijective (policies j)) →
        ∀ y : Fin s → Fin s → Fin s → ℚ,
          (∀ i j k, 0 ≤ y i j k) →
          (∀ (σ : Equiv.Perm (Fin s)) i j k,
            y (σ i) (σ j) (σ k) = y i j k) →
          (∑ i : Fin s, ∑ j : Fin s, ∑ k : Fin s,
            base policies i j k * y i j k) ≤ 0

end MathlibPlus.Open.Probability
