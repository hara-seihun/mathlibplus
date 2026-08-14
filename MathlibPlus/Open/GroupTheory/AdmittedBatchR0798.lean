import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- Claim 24810: a Sylow `p`-subgroup of `S_p^18` is `C_p^18`. -/
def sylowSymmetricProductIsElementaryAbelian : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ P : Sylow p (Fin 18 → Equiv.Perm (Fin p)),
      Nonempty (P ≃* (Fin 18 → Multiplicative (ZMod p)))

end MathlibPlus.Open.GroupTheory
