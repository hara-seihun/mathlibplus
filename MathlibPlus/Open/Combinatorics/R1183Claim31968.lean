import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.Combinatorics.R1183.Claim31968

noncomputable section

open MathlibPlus.Combinatorics.Claim41731

private abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
private abbrev State := Equiv.Perm C7

private def c7Add (x y : C7) : C7 := x + y
private def c7Sub (x y : C7) : C7 := x - y
private def c7Mul (x y : C7) : C7 := x * y

private def shiftedDerivative (r : C7) (δ : State) : C7 → C7 :=
  fun s => c7Sub (δ (c7Add r s)) (δ r)

private def normalizedStateFamily (δ : C7 → State) : Prop :=
  ∀ y : C7, δ y ∈ normalizedStates

private def nonlinearStates : Finset State :=
  normalizedStates \ scalarStates

private def leastBasepoint (X : Finset C7) (a : C7) : Prop :=
  a ∈ X ∧ ∀ x ∈ X, a ≤ x

private def normalizedSupportOffset (X : Finset C7) (a : C7)
    (r : C7 → C7) : Prop :=
  2 ≤ X.card ∧ leastBasepoint X a ∧ r a = 0

private def compatibleStateFamily (X : Finset C7) (r : C7 → C7)
    (δ : C7 → State) : Prop :=
  normalizedStateFamily δ ∧
    ∀ x ∈ X, ∀ x' ∈ X, ∀ y : C7,
      shiftedDerivative (r x) (δ y) =
        shiftedDerivative (r x') (δ (c7Add y (c7Sub x' x)))

/-- Claim 31968: a compatible normalized family contains a nonlinear state
exactly when the support offsets are affine from the least basepoint. -/
def nonlinearCompatibilityIffAffineOffsets31968 : Prop :=
  ∀ (X : Finset C7) (a : C7) (r : C7 → C7),
    normalizedSupportOffset X a r →
      ((∃ δ : C7 → State,
          compatibleStateFamily X r δ ∧
            ∃ y : C7, δ y ∈ nonlinearStates) ↔
        ∃ m : C7, ∀ x ∈ X,
          r x = c7Mul m (c7Sub x a))

end

end MathlibPlus.Open.Combinatorics.R1183.Claim31968
