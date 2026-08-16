import Mathlib

namespace MathlibPlus.Open.Research

/-- The exact cyclic-action permutation construction from claim 60346. -/
def claim60346 : Prop :=
  let V₀ := ZMod 7 × (Fin 2 → ZMod 7)
  let V := Multiplicative V₀
  let C₃ := Multiplicative (ZMod 3)
  (orderOf (2 : ZMod 7) = 3) ∧
    ∃ ρ : C₃ →* MulAut V,
      (∀ x : V₀,
        ρ (Multiplicative.ofAdd (1 : ZMod 3)) (Multiplicative.ofAdd x) =
          Multiplicative.ofAdd ((2 : ZMod 7) • x)) ∧
      ∃ f : Equiv.Perm (V ⋊[ρ] C₃),
        Function.Involutive f ∧
          (∀ (n : Fin 2 → ZMod 7) (i : C₃),
            f ⟨Multiplicative.ofAdd (1, n), i⟩ =
              ⟨Multiplicative.ofAdd (1, n), Multiplicative.ofAdd (-Multiplicative.toAdd i)⟩) ∧
          (∀ (b : ZMod 7) (n : Fin 2 → ZMod 7) (i : C₃), b ≠ 1 →
            f ⟨Multiplicative.ofAdd (b, n), i⟩ =
              ⟨Multiplicative.ofAdd (b, n), i⟩)

end MathlibPlus.Open.Research
