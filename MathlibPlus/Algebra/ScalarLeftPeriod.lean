import Mathlib

namespace MathlibPlus.Algebra.ScalarLeftPeriod

/-- The left-period set of an arbitrary function into `𝔽₅ˣ` is a subgroup;
under normalization at the identity, every period has value one. -/
theorem scalarLeftPeriodSubgroupClaim
    (F : Type*) [Group F] (ell : F → (ZMod 5)ˣ) :
    let Q : Subgroup F :=
      { carrier := {q | ∀ k : F, ell (q * k) = ell k}
        one_mem' := by
          intro k
          simp
        mul_mem' := by
          intro a b ha hb k
          rw [mul_assoc, ha, hb]
        inv_mem' := by
          intro a ha k
          have h := ha (a⁻¹ * k)
          simpa [mul_assoc] using h.symm }
    (∀ q : F, q ∈ Q ↔ ∀ k : F, ell (q * k) = ell k) ∧
      (ell 1 = 1 → ∀ q : F, q ∈ Q → ell q = 1) := by
  dsimp
  constructor
  · intro q
    rfl
  · intro hell q hq
    have h := hq 1
    simpa [hell] using h

end MathlibPlus.Algebra.ScalarLeftPeriod
