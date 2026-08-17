import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a004a9
import MathlibPlus.Open.Research.RegularPrimeBlocks

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1822

abbrev V (p : ℕ) := Fin 5 → ZMod p

/-- The actual regular translation subgroup on the supplied additive carrier. -/
def translationGroup (p : ℕ) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure (Set.range (fun v : V p => Equiv.addRight v))

/-- Conjugation of a permutation subgroup by an actual permutation. -/
def conjugateTranslationGroup {p : ℕ}
    (R : Subgroup (Equiv.Perm (V p))) (q : Equiv.Perm (V p)) :
    Subgroup (Equiv.Perm (V p)) :=
  Subgroup.map (MulAut.conj q⁻¹).toMonoidHom R

/-- A regular elementary-abelian copy of the additive group `F_p^5`. -/
def regularElementaryAbelian (p : ℕ) (hp : Nat.Prime p)
    (H : Subgroup (Equiv.Perm (V p))) : Prop :=
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  MathlibPlus.Open.Research.RegularPrimeBlocks.IsRegularPermutationSubgroup H ∧
    Nonempty (H ≃* Multiplicative (V p))

/-- The uncorrected displayed formula is required to be represented by an
actual permutation, rather than supplied as an unconstrained callback. -/
def uncorrectedLiftPermutation (p : ℕ) (hp : Nat.Prime p)
    (f : ZMod p → ZMod p) (q₀ : Equiv.Perm (V p)) : Prop :=
  ∀ x : V p,
    q₀ x =
      MathlibPlus.Open.ResearchFormalizationBatch.R1822.uncorrectedReplacement
        p hp f x

/-- Claim 32635: the explicitly displayed uncorrected replacement supplies the
source and target regular copies and their generated permutation group. -/
def sourceTargetGeneratedRegularGroups_claim32635 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    ∀ (f : ZMod p → ZMod p),
      MathlibPlus.Open.ResearchFormalizationBatch.R1822.familyOfLiftCorrections
        p hp f →
      ∃ q₀ : Equiv.Perm (V p),
        uncorrectedLiftPermutation p hp f q₀ ∧
          let R := translationGroup p
          let T := conjugateTranslationGroup R q₀
          let G :=
            MathlibPlus.Open.Research.RegularPrimeBlocks.generatedPermutationGroup R T
          regularElementaryAbelian p hp R ∧
            regularElementaryAbelian p hp T ∧
            G =
              MathlibPlus.Open.Research.RegularPrimeBlocks.generatedPermutationGroup R T

/-- The complete displayed family is required to be a family of actual
permutations, with its zeroth member the uncorrected replacement. -/
def liftPermutationFamily (p : ℕ) (hp : Nat.Prime p)
    (f : ZMod p → ZMod p)
    (q : ZMod p → Equiv.Perm (V p)) : Prop :=
  (∀ (lam : ZMod p) (x : V p),
    q lam x =
      MathlibPlus.Open.ResearchFormalizationBatch.R1822.liftCorrection
        p hp f lam x) ∧
  (∀ x : V p,
    q 0 x =
      MathlibPlus.Open.ResearchFormalizationBatch.R1822.uncorrectedReplacement
        p hp f x)

/-- Claim 32638: every member of the explicit `lambda`-indexed permutation
family conjugates the same source translation group onto the target. -/
def everyLinearFiberCorrectionConjugatesTheSamePair_claim32638 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    ∀ (f : ZMod p → ZMod p),
      MathlibPlus.Open.ResearchFormalizationBatch.R1822.familyOfLiftCorrections
        p hp f →
      ∃ q : ZMod p → Equiv.Perm (V p),
        liftPermutationFamily p hp f q ∧
          let R := translationGroup p
          let T := conjugateTranslationGroup R (q 0)
          ∀ lam : ZMod p,
            conjugateTranslationGroup R (q lam) = T

end MathlibPlus.Open.ResearchFormalization.R1822
