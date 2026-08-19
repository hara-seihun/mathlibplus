import MathlibPlus.Open.ResearchFormalization.R1475Claim37638
import MathlibPlus.Open.ResearchFormalization.R1475Claim37641

namespace MathlibPlus.Open.ResearchFormalization.R1475Claim37636

abbrev EPoint (q : ℕ) :=
  MathlibPlus.Open.ResearchFormalization.R1475Claim37638.EPoint q
abbrev Block := Fin 8
abbrev Multiplier (q : ℕ) :=
  MathlibPlus.Open.ResearchFormalization.R1475Claim37638.Multiplier q

open MathlibPlus.Open.ResearchFormalization.R1475Claim37638
open MathlibPlus.Open.ResearchFormalization.R1475Claim37641

/-- Claim 37636: the exact odd-prime pure-multiplier profile, its marked map,
the source regular copy, the conjugated target copy, and the generated pair.
The target and generated-pair carriers are explicit so that `T = R^F` and
`X = ⟨R,T⟩` are retained rather than hidden in unrelated callbacks. -/
def claim37636_pureMultiplierProfileMarkedMap
    (q : ℕ) (a : Multiplier q) (F : Equiv.Perm (EPoint q))
    (R : Subgroup (Equiv.Perm (EPoint q)))
    (T : Set (Equiv.Perm (EPoint q)))
    (X : Subgroup (Equiv.Perm (EPoint q))) : Prop :=
  (Nat.Prime q ∧ Odd q) ∧
    R1475Claim37638.pureMultiplierFormula a F ∧
    R1475Claim37638.sourceRegularCopy q R ∧
    T = R1475Claim37638.conjugatedSet R F ∧
    X = R1475Claim37641.generatedPair R F

end MathlibPlus.Open.ResearchFormalization.R1475Claim37636
