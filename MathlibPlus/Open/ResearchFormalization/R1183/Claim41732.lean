-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib
import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.ResearchFormalization.R1183.Claim41732

noncomputable section

abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
abbrev State := Equiv.Perm C7

/-- The shifted relative derivative on the point-permutation carrier. -/
def shiftedRelativeDerivative_claim41732
    (r : C7) (δ : State) : C7 → C7 :=
  fun s => δ (r + s) - δ r

/-- Pointwise equality to the shifted relative derivative. -/
def derivativeRelation_claim41732
    (r : C7) (δ δ' : State) : Prop :=
  ∀ s : C7, δ' s = shiftedRelativeDerivative_claim41732 r δ s

/-- The derivative action is a bijection from one finite state subset to another,
expressed without introducing an unproved bundled permutation. -/
def permutesByDerivative_claim41732
    (r : C7) (A B : Finset State) : Prop :=
  (∀ δ : State, δ ∈ A →
    ∃! δ' : State, δ' ∈ B ∧ derivativeRelation_claim41732 r δ δ') ∧
    (∀ δ' : State, δ' ∈ B →
      ∃! δ : State, δ ∈ A ∧ derivativeRelation_claim41732 r δ δ')

/-- Claim 41732: every shifted relative derivative permutes the full normalized
state space and separately permutes its scalar and nonlinear subsets. -/
def claim41732 : Prop :=
  MathlibPlus.Combinatorics.Claim41731.normalizedStates.card = 720 ∧
    MathlibPlus.Combinatorics.Claim41731.scalarStates.card = 6 ∧
      (MathlibPlus.Combinatorics.Claim41731.normalizedStates \
        MathlibPlus.Combinatorics.Claim41731.scalarStates).card = 714 ∧
        ∀ r : C7,
          permutesByDerivative_claim41732 r
              MathlibPlus.Combinatorics.Claim41731.normalizedStates
              MathlibPlus.Combinatorics.Claim41731.normalizedStates ∧
            permutesByDerivative_claim41732 r
              MathlibPlus.Combinatorics.Claim41731.scalarStates
              MathlibPlus.Combinatorics.Claim41731.scalarStates ∧
              permutesByDerivative_claim41732 r
                (MathlibPlus.Combinatorics.Claim41731.normalizedStates \
                  MathlibPlus.Combinatorics.Claim41731.scalarStates)
                (MathlibPlus.Combinatorics.Claim41731.normalizedStates \
                  MathlibPlus.Combinatorics.Claim41731.scalarStates)

end

end MathlibPlus.Open.ResearchFormalization.R1183.Claim41732
