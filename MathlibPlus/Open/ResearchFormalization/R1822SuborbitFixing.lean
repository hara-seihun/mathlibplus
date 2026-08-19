import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1822RegularTranslationClaims

namespace MathlibPlus.Open.ResearchFormalization.R1822SuborbitFixing

open MathlibPlus.Open.ResearchFormalization.R1822
open MathlibPlus.Open.ResearchFormalizationBatch.R1822
open MathlibPlus.Open.Research.RegularPrimeBlocks

noncomputable section

/-- The point-stabilizer suborbit of `y` for a permutation subgroup `G` at a
base point `x`. -/
def pointStabilizerSuborbit_claim32643
    {Ω : Type*} (G : Subgroup (Equiv.Perm Ω)) (x y : Ω) : Set Ω :=
  {z | ∃ g : G,
    (g : Equiv.Perm Ω) x = x ∧
      (g : Equiv.Perm Ω) y = z}

/-- Every displayed lift correction fixes every point-stabilizer suborbit of
its actual generated pair. -/
def claim32643 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p)
    (f : ZMod p → ZMod p)
    (q₀ : Equiv.Perm (V p))
    (q : ZMod p → Equiv.Perm (V p)),
    familyOfLiftCorrections p hp f →
    uncorrectedLiftPermutation p hp f q₀ →
    liftPermutationFamily p hp f q →
    let R := translationGroup p
    let T := conjugateTranslationGroup R q₀
    let G := generatedPermutationGroup R T
    ∀ (lam : ZMod p) (y : V p),
      q lam '' pointStabilizerSuborbit_claim32643 G 0 y =
        pointStabilizerSuborbit_claim32643 G 0 y

end
end MathlibPlus.Open.ResearchFormalization.R1822SuborbitFixing
