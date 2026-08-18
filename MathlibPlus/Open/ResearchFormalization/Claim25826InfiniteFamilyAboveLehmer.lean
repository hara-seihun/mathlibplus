import MathlibPlus.Open.ResearchFormalization.BoydBudget25797
import MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim25826InfiniteFamilyAboveLehmer

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydBudget25797
open MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

private def record39Trace (m : ℤ) : Polynomial ℤ :=
  Polynomial.X ^ 3 - Polynomial.C (2 * m + 4) * Polynomial.X ^ 2 +
    Polynomial.C m * Polynomial.X + Polynomial.C 1

private def record39Interlacer (m : ℤ) : Polynomial ℤ :=
  2 * Polynomial.X - Polynomial.C 1

private def record39Correction (m : ℤ) : Polynomial ℤ :=
  Polynomial.X * record39Interlacer m

private def record39Boyd (m : ℤ) : Polynomial ℤ :=
  Polynomial.X ^ 7 - Polynomial.C (2 * m + 6) * Polynomial.X ^ 6 +
    Polynomial.C (m + 4) * Polynomial.X ^ 5 -
    Polynomial.C (4 * m + 9) * Polynomial.X ^ 4 +
    Polynomial.C (m + 3) * Polynomial.X ^ 3 -
    Polynomial.C (2 * m + 2) * Polynomial.X ^ 2 +
    Polynomial.C 2

private def record39IndexRange : Set ℤ :=
  {m | (-1 : ℤ) ≤ m}

private def record39SmallestIndex : Prop :=
  (-1 : ℤ) ∈ record39IndexRange ∧
    ∀ m : ℤ, m ∈ record39IndexRange → (-1 : ℤ) ≤ m

private def realMap (p : Polynomial ℤ) : Polynomial ℝ :=
  p.map (algebraMap ℤ ℝ)

private def record39SmallestData : Prop :=
  let m : ℤ := -1
  let ell : Polynomial ℝ := realMap (record39Trace m)
  let d : Polynomial ℝ := realMap (record39Interlacer m)
  let c : Polynomial ℝ := realMap (record39Correction m)
  let q : Polynomial ℝ := ell - (2 : Polynomial ℝ) * c
  let A : Polynomial ℝ := realMap (record39Boyd m)
  record39SmallestIndex ∧
    Polynomial.resultant (record39Trace m) (record39Interlacer m) = (-1 : ℤ) ∧
    ¬ Polynomial.Monic (record39Interlacer m) ∧
    affineBoydFormula 3 ell c q A ∧
    ∃ θ : ℝ,
      BoydBudget25797.exteriorRoot A θ

/-- Claim 25826: the explicit smallest `m=-1` member of Record 39 has a
unit-resultant nonmonic interlacer and an exterior trace root above `11/5`,
while Lehmer's exterior trace root lies below `21/10`; the two strict bounds
therefore place this family above, rather than below, Lehmer. -/
def claim25826 : Prop :=
  record39SmallestData ∧
    ∃ TRecord TLehmer : ℝ,
      BoydBudget25797.exteriorTraceRoot
        (realMap (record39Trace (-1 : ℤ))) TRecord ∧
      (11 / 5 : ℝ) < TRecord ∧
      BoydBudget25797.exteriorTraceRoot lehmerTrace TLehmer ∧
      TLehmer < (21 / 10 : ℝ) ∧
      TLehmer < TRecord

end

end MathlibPlus.Open.ResearchFormalization.Claim25826InfiniteFamilyAboveLehmer
