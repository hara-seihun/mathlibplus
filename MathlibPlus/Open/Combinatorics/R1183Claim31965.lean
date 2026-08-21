-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.Combinatorics.R1183.Claim31965

noncomputable section

open MathlibPlus.Combinatorics.Claim41731

private abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
private abbrev State := Equiv.Perm C7

private def c7Add (x y : C7) : C7 := x + y
private def c7Sub (x y : C7) : C7 := x - y

private def shiftedDerivative (r : C7) (δ : State) : C7 → C7 :=
  fun s => c7Sub (δ (c7Add r s)) (δ r)

private def derivativeRelation (r : C7) (δ δ' : State) : Prop :=
  ∀ s : C7, δ' s = shiftedDerivative r δ s

private def nonlinearStates : Finset State :=
  normalizedStates \ scalarStates

/-- Claim 31965: every shifted relative derivative permutes the normalized
C₇ states and preserves the scalar/nonlinear partition. -/
def shiftedRelativeDerivativePermutes31965 : Prop :=
  normalizedStates.card = 720 ∧
    scalarStates.card = 6 ∧
      nonlinearStates.card = 714 ∧
        ∀ r : C7,
          (∀ δ ∈ normalizedStates,
            ∃! δ' : State,
              δ' ∈ normalizedStates ∧ derivativeRelation r δ δ') ∧
            (∀ δ' ∈ normalizedStates,
              ∃ δ ∈ normalizedStates, derivativeRelation r δ δ') ∧
            (∀ δ δ' : State,
              δ ∈ normalizedStates →
                δ' ∈ normalizedStates →
                  derivativeRelation r δ δ' →
                    ((δ ∈ scalarStates ↔ δ' ∈ scalarStates) ∧
                      (δ ∈ nonlinearStates ↔ δ' ∈ nonlinearStates)))

end

end MathlibPlus.Open.Combinatorics.R1183.Claim31965
