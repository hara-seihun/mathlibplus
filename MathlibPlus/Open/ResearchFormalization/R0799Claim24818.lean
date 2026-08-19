import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch.R0799Claim24822

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch.R0799Claim24818

noncomputable section

private abbrev Poly := MvPolynomial (Option ℕ) ℤ

private def variableExponent (lam : Multiset ℕ) : Option ℕ →₀ ℕ :=
  (lam.map (fun i : ℕ =>
    (Finsupp.single (some i) 1 : Option ℕ →₀ ℕ))).sum

private def monomialExponent (a : ℕ) (lam : Multiset ℕ) : Option ℕ →₀ ℕ :=
  Finsupp.single none a + variableExponent lam

private def additiveDefect (e : Option ℕ →₀ ℕ) : ℕ :=
  e none +
    e.support.sum (fun q =>
      match q with
      | none => 0
      | some i => e (some i) * (i - 1))

private def monomialDefect (a : ℕ) (lam : Multiset ℕ) : ℕ :=
  additiveDefect (monomialExponent a lam)

private def defectLayer (p : Poly) (j : ℕ) : Poly :=
  (p.support.filter (fun e => additiveDefect e = j)).sum
    (fun e => MvPolynomial.monomial e (p.coeff e))

/-- Claim 24818: the defect of the monomial `z^a x_λ` is additive in the
root variable and the indexed ordinary variables, using the same exponent
carrier as the reviewed rooted-factor defect layers. -/
def claim24818_additiveMonomialDefect : Prop :=
  ∀ (a : ℕ) (lam : Multiset ℕ),
    monomialDefect a lam =
      a + (lam.map (fun i : ℕ => i - 1)).sum

end

end MathlibPlus.Open.Research.FormalizationBatch.R0799Claim24818
