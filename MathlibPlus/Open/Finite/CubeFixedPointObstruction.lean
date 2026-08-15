import Mathlib

namespace MathlibPlus.Open

/-- Claim 28556: the order-nine obstruction in the degree-144 product action. -/
def cubeFixedPointObstructionInTwelveByTwelve : Prop :=
  let baseAction :=
    fun (a b : Equiv.Perm (Fin 12)) =>
      Equiv.prodCongr a b
  let wreathAction :=
    fun (a b : Equiv.Perm (Fin 12)) (σ : Equiv.Perm (Fin 2)) =>
      if σ = (1 : Equiv.Perm (Fin 2)) then
        baseAction a b
      else
        (baseAction a b).trans (Equiv.prodComm (Fin 12) (Fin 12))
  ∀ (a b : Equiv.Perm (Fin 12)) (σ : Equiv.Perm (Fin 2)),
    orderOf (wreathAction a b σ) = 9 →
      σ = (1 : Equiv.Perm (Fin 2)) ∧
        wreathAction a b σ = baseAction a b ∧
        (∀ x : Fin 12,
          a x = x ∨
            (((a ^ 3) x = x) ∧ (a x ≠ x)) ∨
            (((a ^ 9) x = x) ∧ ((a ^ 3) x ≠ x))) ∧
        (∀ x : Fin 12,
          b x = x ∨
            (((b ^ 3) x = x) ∧ (b x ≠ x)) ∨
            (((b ^ 9) x = x) ∧ ((b ^ 3) x ≠ x))) ∧
        Fintype.card
              {x : Fin 12 // (a ^ 3) x = x} ≥ 3 ∧
        Fintype.card
              {x : Fin 12 // (b ^ 3) x = x} ≥ 3 ∧
        Fintype.card
              {x : Fin 12 × Fin 12 //
                (baseAction a b ^ 3) x = x} ≥ 9 ∧
        ∀ K : Subgroup (Equiv.Perm (Fin 12 × Fin 12)),
          (∀ x y : Fin 12 × Fin 12,
            ∃! k : K, (k : Equiv.Perm (Fin 12 × Fin 12)) x = y) →
          baseAction a b ^ 3 ∈ K →
          baseAction a b ^ 3 = 1

end MathlibPlus.Open
