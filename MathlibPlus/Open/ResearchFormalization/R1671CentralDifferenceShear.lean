import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1671CentralDifferenceShear

noncomputable section

/-- Claim 33133: the coordinate-level central difference shear on the exact
six-dimensional `F_p` carrier is a permutation for every function `n`; the
explicit subtraction formula is its two-sided inverse. -/
def arbitraryCentralDifferenceShear_claim33133 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ n : ZMod p → ZMod p,
      let F : (Fin 6 → ZMod p) → (Fin 6 → ZMod p) :=
        fun x =>
          ![x 0, x 1, x 2 + n (x 0 + x 4), x 3, x 4,
            x 5 + n (x 0 + x 4)]
      let G : (Fin 6 → ZMod p) → (Fin 6 → ZMod p) :=
        fun x =>
          ![x 0, x 1, x 2 - n (x 0 + x 4), x 3, x 4,
            x 5 - n (x 0 + x 4)]
      (∀ x, G (F x) = x) ∧ (∀ x, F (G x) = x)

end

end MathlibPlus.Open.ResearchFormalization.R1671CentralDifferenceShear
