import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.DeltaPropagationExact

noncomputable section

private abbrev PositiveIndex := ℕ+
private abbrev RootRing := Polynomial (MvPolynomial PositiveIndex ℚ)
private abbrev CoefficientRing := MvPolynomial PositiveIndex ℚ

private def rootZ : RootRing := Polynomial.X

private def rootX (k : PositiveIndex) : RootRing :=
  Polynomial.C (MvPolynomial.X k)

private def rootClosure (P : RootRing) : RootRing :=
  rootZ * P +
    P.support.sum (fun k =>
      Polynomial.C (MvPolynomial.X (Nat.succPNat k) * P.coeff k))

private def rootStable (S : Subalgebra ℚ RootRing) : Prop :=
  ∀ P : RootRing, P ∈ S → rootClosure P ∈ S

private def scalarAlgebra : Subalgebra ℚ RootRing :=
  sInf {S : Subalgebra ℚ RootRing | rootStable S}

private def positiveOne : PositiveIndex := 1

private abbrev DeltaIndex := {k : PositiveIndex // 2 ≤ (k : ℕ)}

private def delta (k : DeltaIndex) : RootRing :=
  rootX k.1 - rootZ ^ ((k : ℕ) - 1) * rootX positiveOne

private def deltaProduct (e : DeltaIndex →₀ ℕ) : RootRing :=
  e.prod (fun k a => delta k ^ a)

/-- The extracted delta generators propagate under the scalar rooted-factor
algebra, and every ambient monomial with a delta factor lies in that algebra. -/
def claim23322 : Prop :=
  (∀ k : DeltaIndex, delta k ∈ scalarAlgebra) ∧
    (∀ k : DeltaIndex, ∀ a b : ℕ,
      rootZ ^ a * rootX positiveOne ^ b * delta k ∈ scalarAlgebra) ∧
    (∀ a b : ℕ, ∀ e : DeltaIndex →₀ ℕ,
      e.support.Nonempty →
        rootZ ^ a * rootX positiveOne ^ b * deltaProduct e ∈ scalarAlgebra)

end
end MathlibPlus.Open.Research.DeltaPropagationExact
