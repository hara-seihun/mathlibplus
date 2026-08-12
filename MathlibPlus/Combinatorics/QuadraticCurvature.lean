import Mathlib

namespace MathlibPlus.Combinatorics.QuadraticCurvature

/-- Claim 5178: the quadratic curvature identity in every field.

The extracted sentence does not define `χ`; in the source vocabulary it is the
curvature `χ = 2 - d`.  That convention is made explicit by the local binding
rather than being introduced as an unstated hypothesis. -/
theorem quadraticCurvatureIdentity (K : Type*) [Field K] (d : ℕ) :
    let χ : K := 2 - (d : K)
    (2 : K) * (Nat.choose d 2 : K) = χ ^ 2 - 3 * χ + 2 := by
  dsimp
  have hchoose : (2 : K) * (Nat.choose d 2 : K) =
      (d : K) * ((d : K) - 1) := by
    induction d with
    | zero => norm_num
    | succ d ih =>
      simp only [Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.cast_add, Nat.cast_one]
      change (2 : K) * ((d : K) + (Nat.choose d 2 : K)) =
        ((d : K) + 1) * ((d : K) + 1 - 1)
      rw [mul_add, ih]
      ring
  rw [hchoose]
  ring

end MathlibPlus.Combinatorics.QuadraticCurvature
