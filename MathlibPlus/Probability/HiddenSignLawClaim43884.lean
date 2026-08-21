-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.Open.Basic

open scoped BigOperators

namespace MathlibPlus.Open.Probability

/-- An exact 16-state hidden-sign law with three conditionally independent
observations, each agreeing with the hidden sign with probability `15/16`. -/
def hiddenSignLaw_claim43884 : Prop :=
  ∃ (p : Fin 16 → ℚ) (θ : Fin 16 → Bool)
    (X : Fin 3 → Fin 16 → Bool) (Z : Fin 16 → ℚ),
    (∀ ω, 0 ≤ p ω) ∧
    (∑ ω, p ω = 1) ∧
    (∀ b : Bool,
      ∑ ω ∈ Finset.univ.filter (fun ω => θ ω = b), p ω = (1 / 2 : ℚ)) ∧
    (∀ b : Bool, ∀ x : Fin 3 → Bool,
      ∑ ω ∈ Finset.univ.filter
          (fun ω => θ ω = b ∧ ∀ i, X i ω = x i), p ω =
        (1 / 2 : ℚ) * ∏ i, if x i = b then (15 / 16 : ℚ) else (1 / 16 : ℚ)) ∧
    (∀ ω, Z ω =
      ((if X 0 ω then (1 : ℚ) else -1) +
        (if X 1 ω then (1 : ℚ) else -1) +
        (if X 2 ω then (1 : ℚ) else -1)) / 3)

end MathlibPlus.Open.Probability

namespace MathlibPlus.Probability

theorem hiddenSignLaw_claim43884_proof :
    MathlibPlus.Open.Probability.hiddenSignLaw_claim43884 := by
  let bit : Nat → Nat → Bool :=
    fun n k => decide (((n / 2 ^ k) % 2) = 1)
  let θ : Fin 16 → Bool := fun ω => bit ω.val 3
  let X : Fin 3 → Fin 16 → Bool :=
    fun i ω => Bool.xor (θ ω) (bit ω.val i.val)
  let p : Fin 16 → ℚ := fun ω =>
    (1 / 2 : ℚ) * ∏ i : Fin 3,
      if bit ω.val i.val then (1 / 16 : ℚ) else (15 / 16 : ℚ)
  let Z : Fin 16 → ℚ := fun ω =>
    ((if X 0 ω then (1 : ℚ) else -1) +
      (if X 1 ω then (1 : ℚ) else -1) +
      (if X 2 ω then (1 : ℚ) else -1)) / 3
  refine ⟨p, θ, X, Z, ?_⟩
  native_decide

end MathlibPlus.Probability
