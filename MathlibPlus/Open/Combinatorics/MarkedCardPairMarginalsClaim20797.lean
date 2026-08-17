import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Claim 20797: the three one-coordinate marginals do not determine a joint
binary common-count block, and hence no linear left inverse recovers that
block from the strengthened marked output. -/
def strengthenedMarkedCardPairMap_not_injective_claim20797 : Prop :=
  let Tensor := Fin 2 → Fin 2 → Fin 2 → ℤ
  let Marginals := (Fin 2 → ℤ) × (Fin 2 → ℤ) × (Fin 2 → ℤ)
  let Φ : Tensor → Marginals := fun U =>
    ((fun r => ∑ p : Fin 2, ∑ q : Fin 2, U p q r),
      (fun q => ∑ p : Fin 2, ∑ r : Fin 2, U p q r),
      (fun p => ∑ q : Fin 2, ∑ r : Fin 2, U p q r))
  let Tplus : Tensor :=
    fun p q r => 1 + (-1 : ℤ) ^ (p.val + q.val + r.val)
  let Tminus : Tensor :=
    fun p q r => 1 - (-1 : ℤ) ^ (p.val + q.val + r.val)
  ¬ Function.Injective Φ ∧
    Tplus ≠ Tminus ∧
    Φ Tplus = Φ Tminus ∧
    ¬ ∃ R : Marginals →ₗ[ℤ] Tensor, ∀ T : Tensor, R (Φ T) = T

end MathlibPlus.Open.Combinatorics
