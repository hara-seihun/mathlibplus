import MathlibPlus.Combinatorics.Claim41731

namespace MathlibPlus.Open.Combinatorics.R1183.Claim31967

noncomputable section

open MathlibPlus.Combinatorics.Claim41731

private abbrev C7 := MathlibPlus.Combinatorics.Claim41731.C7
private abbrev State := Equiv.Perm C7

private def c7Add (x y : C7) : C7 := x + y
private def c7Sub (x y : C7) : C7 := x - y

private def shiftedDerivative (r : C7) (δ : State) : C7 → C7 :=
  fun s => c7Sub (δ (c7Add r s)) (δ r)

private def normalizedStateFamily (δ : C7 → State) : Prop :=
  ∀ y : C7, δ y ∈ normalizedStates

private def scalarStateFamily (δ : C7 → State) : Prop :=
  ∀ y : C7, δ y ∈ scalarStates

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

/-- Claim 31967: every normalized support-offset assignment has exactly the
six compatible constant scalar state families. -/
def sixCompatibleConstantScalarFamilies31967 : Prop :=
  ∀ (X : Finset C7) (a : C7) (r : C7 → C7),
    normalizedSupportOffset X a r →
      scalarStates.card = 6 ∧
        (∀ σ : State, σ ∈ scalarStates →
          compatibleStateFamily X r (fun _ : C7 => σ)) ∧
        (∀ δ : C7 → State,
          compatibleStateFamily X r δ →
            scalarStateFamily δ →
              ∃ σ : State, σ ∈ scalarStates ∧
                ∀ y : C7, δ y = σ)

end

end MathlibPlus.Open.Combinatorics.R1183.Claim31967
