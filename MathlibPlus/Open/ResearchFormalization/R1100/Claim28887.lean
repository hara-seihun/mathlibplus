import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationR1100

/-- Claim 28887: the normalized and arbitrary-constant table carriers have
 the stated exact cardinalities.  Each carrier records rank two, a nonzero
 translation period, and its full one-dimensional period subspace. -/
def periodicTableCounts_claim28887 : Prop :=
  Nat.card
      {F : (Fin 2 → ZMod 3) → (Fin 3 → ZMod 3) //
        F 0 = 0 ∧
          Module.finrank (ZMod 3)
              (Submodule.span (ZMod 3) (Set.range (fun x => F x - F 0))) = 2 ∧
          (∃ s : Fin 2 → ZMod 3, s ≠ 0 ∧ ∀ x, F (x + s) = F x) ∧
          ∃ K : Submodule (ZMod 3) (Fin 2 → ZMod 3),
            Module.finrank (ZMod 3) K = 1 ∧
              K ≠ ⊤ ∧
              ∀ s, s ∈ K ↔ ∀ x, F (x + s) = F x} =
    4 * 624 ∧
  Nat.card
      {F : (Fin 2 → ZMod 3) → (Fin 3 → ZMod 3) //
        ∃ c : Fin 3 → ZMod 3,
          F 0 = c ∧
            (fun x => F x - c) 0 = 0 ∧
            Module.finrank (ZMod 3)
                (Submodule.span (ZMod 3)
                  (Set.range (fun x => (F x - c) - (F 0 - c)))) = 2 ∧
            (∃ s : Fin 2 → ZMod 3,
              s ≠ 0 ∧ ∀ x, (F (x + s) - c) = (F x - c)) ∧
            ∃ K : Submodule (ZMod 3) (Fin 2 → ZMod 3),
              Module.finrank (ZMod 3) K = 1 ∧
                K ≠ ⊤ ∧
                ∀ s, s ∈ K ↔
                  ∀ x, (F (x + s) - c) = (F x - c)} =
      27 * (4 * 624)

end MathlibPlus.Open.ResearchFormalizationR1100
