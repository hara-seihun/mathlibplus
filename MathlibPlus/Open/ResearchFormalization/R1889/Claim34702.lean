import MathlibPlus.Open.RootedTreeBoundary

namespace MathlibPlus.Open.ResearchFormalization.R1889

open MathlibPlus.Open.RootedTreeBoundary

/-- Claim 34702: the actual rooted boundary factor has the displayed
specialization and every resulting `L_R` has the universal factor. -/
def claim34702 : Prop :=
  ∀ R : RootedFiniteTree,
    let B : Polynomial (Polynomial ℤ) :=
      R.normalizedBoundaryFactor ℤ
    let u : Polynomial (Polynomial ℤ) := Polynomial.X
    let v : Polynomial ℤ := Polynomial.X
    let boundaryV : Polynomial (Polynomial ℤ) := Polynomial.C v
    let L : Polynomial (Polynomial ℤ) := u * B + boundaryV - 1
    let factor : Polynomial (Polynomial ℤ) := u + boundaryV - 1
    Polynomial.eval (1 - v) B = 1 ∧
      Polynomial.eval (1 - v) L = 0 ∧
      factor ∣ L

end MathlibPlus.Open.ResearchFormalization.R1889
