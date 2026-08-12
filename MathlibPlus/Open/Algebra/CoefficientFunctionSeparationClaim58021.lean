import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace MathlibPlus.Algebra

/-- The two endpoint coefficient functions in claim 58021 vanish identically. -/
theorem coefficientFunction_one_claim58021 (p : ℕ) (t : ZMod p) :
    (t + 1) ^ 1 - t ^ 1 - 1 = 0 := by
  ring

/-- The characteristic-`p` endpoint coefficient function in claim 58021
vanishes identically. -/
theorem coefficientFunction_prime_claim58021 {p : ℕ} [Fact p.Prime]
    (t : ZMod p) :
    (t + 1) ^ p - t ^ p - 1 = 0 := by
  rw [ZMod.pow_card, ZMod.pow_card]
  ring

end MathlibPlus.Algebra

namespace MathlibPlus.Open.Algebra

/-- Claim 58021 (S1), with `F_p` represented by `ZMod p`.  The functions with
indices `2, ..., p - 1` are indexed by `Fin (p - 2)`, and the rank clause uses
the transpose so that the displayed functions are the matrix columns. -/
def coefficientFunctionSeparation_claim58021 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), 5 ≤ p →
    letI : Fact p.Prime := ⟨hp⟩
    let c : ℕ → ZMod p → ZMod p := fun m t => (t + 1) ^ m - t ^ m - 1
    (∀ t : ZMod p, c 1 t = 0) ∧
      (∀ t : ZMod p, c p t = 0) ∧
      LinearIndependent (ZMod p)
        (fun i : Fin (p - 2) => c (i.val + 2)) ∧
      Matrix.rank
          (Matrix.transpose
            (fun i : Fin (p - 2) =>
              fun t : ZMod p => c (i.val + 2) t)) = p - 2

end MathlibPlus.Open.Algebra
