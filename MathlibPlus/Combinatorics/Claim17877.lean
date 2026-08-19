import Mathlib

namespace MathlibPlus.Combinatorics.Claim17877

/-- The sign of a finite permutation is the product of the signs contributed by
its cycle lengths; a fixed-point cycle contributes `-(-1 : ℤˣ) = 1`. -/
theorem sign_eq_cycle_product_claim17877 {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ =
      (σ.cycleType.map (fun ℓ : ℕ => -(-1 : ℤˣ) ^ ℓ)).prod := by
  exact Equiv.Perm.sign_of_cycleType' σ

end MathlibPlus.Combinatorics.Claim17877
