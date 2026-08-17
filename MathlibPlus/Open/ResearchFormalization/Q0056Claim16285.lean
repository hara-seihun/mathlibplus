import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

open scoped BigOperators
open BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Q0056Claim16285

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

/-- The exact parity-dependent mass appearing in the coloured residual bound. -/
def forbiddenColourMass (s : ℕ) : ℝ :=
  if Even s then
    (s : ℝ) * ((s : ℝ) - 2) * ((s : ℝ) - 4) / 24
  else
    ((s : ℝ) - 1) * ((s : ℝ) - 2) * ((s : ℝ) - 3) / 24

/-- The colours occurring on an indexed residual triple. -/
def residualTripleColours {α : Type*} [DecidableEq α]
    {s : ℕ} (colour : Fin s → α) (I : Fin 3 → Fin s) : Finset α :=
  (Finset.univ : Finset (Fin 3)).image (fun j => colour (I j))

/-- A coloured occurrence system has no repeated colour-set pair and retains
 the pairwise-intersecting residual carrier and its at-most-`r+1` colour bound.
 Its indexed residual sunflowers are required to be neither monochromatic nor
 three-coloured. -/
def noOneOrThreeColourResidualSunflower
    {α : Type*} [DecidableEq α] {s r : ℕ}
    (A : Fin s → Finset α) (colour : Fin s → α) : Prop :=
  (∀ i, ∀ j, i ≠ j →
    (A i ≠ A j ∨ colour i ≠ colour j)) ∧
  (∀ i, ∀ j, i ≠ j → (A i ∩ A j).Nonempty) ∧
  (Finset.univ.image colour).card ≤ r + 1 ∧
  ∀ I : Fin 3 → Fin s, Function.Injective I →
    isSunflowerTuple (fun j => A (I j)) →
      (residualTripleColours colour I).card ≠ 1 ∧
        (residualTripleColours colour I).card ≠ 3

/-- Forbidden colour patterns force the exact incidence-mass lower bounds. -/
def forbiddenColourPatterns_force_incidence_mass_16285 : Prop :=
  ∀ (α : Type*) [DecidableEq α] (s r : ℕ)
    (A : Fin s → Finset α) (colour : Fin s → α),
    (∀ i, (A i).card = r) →
      noOneOrThreeColourResidualSunflower (r := r) A colour →
      forbiddenColourMass s ≤
        ∑ x ∈ indexedGround A,
          ((Nat.choose (tupleIncidenceCount A x) 2 : ℕ) : ℝ) *
            ((s - tupleIncidenceCount A x : ℕ) : ℝ) ∧
      (2 * forbiddenColourMass s) / (s : ℝ) ≤
        ∑ x ∈ indexedGround A,
          ((tupleIncidenceCount A x *
              (tupleIncidenceCount A x - 1) : ℕ) : ℝ)

end
end MathlibPlus.Open.ResearchFormalization.Q0056Claim16285
