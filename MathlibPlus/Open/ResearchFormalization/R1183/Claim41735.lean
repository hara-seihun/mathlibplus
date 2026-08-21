-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib
import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.ResearchFormalization.R1183.Claim41735

noncomputable section

abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
abbrev State := Equiv.Perm C7

/-- The shifted relative derivative on normalized point states. -/
def shiftedRelativeDerivative_claim41735
    (r : C7) (δ : State) : C7 → C7 :=
  fun s => δ (r + s) - δ r

/-- Compatibility for a normalized state family over a support and its offset
assignment. -/
def compatibleFamily_claim41735
    (X : Set C7) (r : X → C7) (δ : C7 → State) : Prop :=
  (∀ y : C7, δ y ∈ MathlibPlus.Combinatorics.Claim41731.normalizedStates) ∧
    ∀ (x x' : X) (y : C7),
      shiftedRelativeDerivative_claim41735 (r x) (δ y) =
        shiftedRelativeDerivative_claim41735 (r x')
          (δ (y + x'.1 - x.1))

/-- A family contains a nonlinear normalized state when one of its values lies
in the complement of the scalar subset of the normalized state space. -/
def containsNonlinearState_claim41735
    (δ : C7 → State) : Prop :=
  ∃ y : C7,
    δ y ∈ (MathlibPlus.Combinatorics.Claim41731.normalizedStates \
      MathlibPlus.Combinatorics.Claim41731.scalarStates)

/-- Claim 41735: a compatible family containing a nonlinear state exists
exactly for affine support offsets anchored at the least support point. -/
def claim41735 : Prop :=
  ∀ (X : Set C7) (a : X)
    (hX : 2 ≤ X.ncard)
    (hleast : ∀ x : X, a.1 ≤ x.1)
    (r : X → C7)
    (hanchor : r a = 0),
    (∃ δ : C7 → State,
      compatibleFamily_claim41735 X r δ ∧
        containsNonlinearState_claim41735 δ) ↔
      ∃ m : C7, ∀ x : X, r x = m * (x.1 - a.1)

end

end MathlibPlus.Open.ResearchFormalization.R1183.Claim41735
