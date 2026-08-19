import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12278

/--
The finite-dimensional characteristic-polynomial and finite-spectrum statement
of Claim 12278.  The characteristic polynomial is the determinant polynomial
of `s I - Θ`; its monicity and full degree record algebraic multiplicity, while
`Set.Finite` records finiteness of the eigenvalue set.
-/
def finiteRankGeneratorHasFinitePolynomialSpectrum : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Θ : Module.End K V),
    Θ.charpoly.Monic ∧
      Θ.charpoly.natDegree = Module.finrank K V ∧
      Set.Finite (fun x : K => Θ.HasEigenvalue x)

end MathlibPlus.LinearAlgebra.Claim12278
