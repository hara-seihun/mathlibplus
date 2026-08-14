import Mathlib

namespace MathlibPlus.Open.JacobsthalClaims

open scoped BigOperators

abbrev PrimeBelow (X : ℕ) := {p : ℕ // Nat.Prime p ∧ p ≤ X}

abbrev ResidueChoice (X : ℕ) := ∀ p : PrimeBelow X, Fin p.1

def CoversInitialInterval (X : ℕ) (a : ResidueChoice X) (Y : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 1 Y, ∃ p : PrimeBelow X, n % p.1 = (a p).1

def SomeResidueChoiceCovers (X Y : ℕ) : Prop :=
  ∃ a : ResidueChoice X, CoversInitialInterval X a Y

noncomputable def primeResidueCoveringLength (X : ℕ) : ℕ :=
  sSup {Y : ℕ | SomeResidueChoiceCovers X Y}

def jacobsthal_prime_residue_covering_function : Prop :=
  ∀ X : ℕ,
    SomeResidueChoiceCovers X (primeResidueCoveringLength X) ∧
      ∀ Y : ℕ, SomeResidueChoiceCovers X Y →
        Y ≤ primeResidueCoveringLength X

noncomputable def primorial (X : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (X + 1)).filter Nat.Prime, p

def HasCoprimeInEveryIntegerInterval (n length : ℕ) : Prop :=
  ∀ a : ℤ, ∃ z : ℤ,
    a ≤ z ∧ z < a + length ∧ Nat.Coprime z.natAbs n

noncomputable def jacobsthalFunction (n : ℕ) : ℕ :=
  sInf {length : ℕ | HasCoprimeInEveryIntegerInterval n length}

def primorial_jacobsthal_equivalence : Prop :=
  ∀ X : ℕ,
    primeResidueCoveringLength X = jacobsthalFunction (primorial X) - 1

def known_quadratic_upper_bound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Filter.Eventually (fun X : ℕ =>
      (primeResidueCoveringLength X : ℝ) ≤ C * (X : ℝ) ^ 2) Filter.atTop

def known_lower_bound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Filter.Eventually (fun X : ℕ =>
      c * (X : ℝ) * Real.log (X : ℝ) *
          Real.log (Real.log (Real.log (X : ℝ))) /
            Real.log (Real.log (X : ℝ)) ≤
        (primeResidueCoveringLength X : ℝ)) Filter.atTop

noncomputable def inverseCoveringFunction (Y : ℕ) : ℕ :=
  sInf {X : ℕ | SomeResidueChoiceCovers X Y}

def inverse_covering_subquadratic_translation : Prop :=
  (Filter.Tendsto
      (fun X : ℕ => (primeResidueCoveringLength X : ℝ) / (X : ℝ) ^ 2)
      Filter.atTop (nhds 0)) ↔
    (Filter.Tendsto
      (fun Y : ℕ => (inverseCoveringFunction Y : ℝ) /
        Real.sqrt (Y : ℝ))
      Filter.atTop Filter.atTop)

end MathlibPlus.Open.JacobsthalClaims
