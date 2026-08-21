-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib
import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.ResearchFormalization.R1183.Claim41734

noncomputable section

abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
abbrev State := Equiv.Perm C7

/-- The shifted relative derivative on normalized point states. -/
def shiftedRelativeDerivative_claim41734
    (r : C7) (δ : State) : C7 → C7 :=
  fun s => δ (r + s) - δ r

/-- Compatibility for a normalized state family over a support and its offset
assignment. -/
def compatibleFamily_claim41734
    (X : Set C7) (r : X → C7) (δ : C7 → State) : Prop :=
  (∀ y : C7, δ y ∈ MathlibPlus.Combinatorics.Claim41731.normalizedStates) ∧
    ∀ (x x' : X) (y : C7),
      shiftedRelativeDerivative_claim41734 (r x) (δ y) =
        shiftedRelativeDerivative_claim41734 (r x')
          (δ (y + x'.1 - x.1))

/-- A constant family whose common state is scalar. -/
def constantScalarFamily_claim41734
    (δ : C7 → State) : Prop :=
  ∃ σ : State,
    σ ∈ MathlibPlus.Combinatorics.Claim41731.scalarStates ∧
      ∀ y : C7, δ y = σ

/-- Claim 41734: every normalized support-offset assignment has exactly the six
compatible constant scalar state families. -/
def claim41734 : Prop :=
  ∀ (X : Set C7) (a : X)
    (hX : 2 ≤ X.ncard)
    (hleast : ∀ x : X, a.1 ≤ x.1)
    (r : X → C7)
    (hanchor : r a = 0),
    Set.ncard
        {δ : C7 → State |
          compatibleFamily_claim41734 X r δ ∧
            constantScalarFamily_claim41734 δ} = 6

end

end MathlibPlus.Open.ResearchFormalization.R1183.Claim41734
