import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0613Claim23315

noncomputable section

abbrev PositiveIndex := ℕ+
abbrev CoefficientRing := MvPolynomial PositiveIndex ℚ
abbrev RootRing := Polynomial CoefficientRing

def rootZ : RootRing := Polynomial.X

def rootX (k : PositiveIndex) : RootRing :=
  Polynomial.C (MvPolynomial.X k)

/-- The finite-support polynomial form of
`B(P)=zP+sum_{k>=0} x_(k+1) p_k(x)`. -/
def rootClosure (P : RootRing) : RootRing :=
  rootZ * P +
    P.support.sum (fun k =>
      Polynomial.C (MvPolynomial.X (Nat.succPNat k) * P.coeff k))

def rootStable (S : Subalgebra ℚ RootRing) : Prop :=
  ∀ P : RootRing, P ∈ S → rootClosure P ∈ S

def scalarRootedFactorAlgebra : Subalgebra ℚ RootRing :=
  sInf {S : Subalgebra ℚ RootRing | rootStable S}

/-- The exact positive-index polynomial carrier, closure operator, and least
stable scalar rooted-factor subalgebra. -/
def claim23315 : Prop :=
  (1 : RootRing) ∈ scalarRootedFactorAlgebra ∧
    rootStable scalarRootedFactorAlgebra ∧
    (∀ S : Subalgebra ℚ RootRing,
      (1 : RootRing) ∈ S → rootStable S →
        scalarRootedFactorAlgebra ≤ S)

end

end MathlibPlus.Open.ResearchFormalization.R0613Claim23315
