import MathlibPlus.Algebra.Claim20663
import MathlibPlus.Open.ResearchFormalization.BoydAffineBatch

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.Claim29530

noncomputable section

private noncomputable def integerMahlerMeasure (P : Polynomial ℤ) : ℝ :=
  Polynomial.mahlerMeasure (P.map (algebraMap ℤ ℂ))

private def nonCyclotomicInteger (P : Polynomial ℤ) : Prop :=
  ∀ n : ℕ, P ≠ Polynomial.cyclotomic n ℤ

private def strictSubLehmer (P : Polynomial ℤ) : Prop :=
  P.Monic ∧
    Irreducible P ∧
      nonCyclotomicInteger P ∧
        1 < integerMahlerMeasure P ∧
          integerMahlerMeasure P <
            MathlibPlus.Algebra.Claim20663.lehmerNumber

private def degree56OneExteriorStrictSubLehmer
    (P ell : Polynomial ℤ) : Prop :=
  strictSubLehmer P ∧
    MathlibPlus.Open.ResearchFormalization.isSalemPolynomial P 28 ∧
      MathlibPlus.Open.ResearchFormalization.traceLift P ell 28

private def shiftedTracePolynomial (ell : Polynomial ℤ) : Polynomial ℤ :=
  ell.comp (Polynomial.X - Polynomial.C (2 : ℤ))

private def polynomialTrace (Q : Polynomial ℤ) : ℤ :=
  -Q.coeff 27

/-- Claim 29530: a hypothetical degree-56 one-exterior strict sub-Lehmer
polynomial yields the exact degree-28 integer trace polynomial with one
exterior root, twenty-seven interior roots, and the certified trace and
endpoint slices.  The finite slice parameters are retained without replacing
this family by an enumerated polynomial list. -/
def finiteTraceAndEndpointFrontierReduction_claim29530 : Prop :=
  ∀ (P ell : Polynomial ℤ),
    degree56OneExteriorStrictSubLehmer P ell →
      let Q := shiftedTracePolynomial ell
      Q.Monic ∧
        Q.natDegree = 28 ∧
          ∃ (δ : ℝ) (α : Fin 27 → ℝ),
            0 < δ ∧
              δ < (27 : ℝ) / 1000 ∧
                (∀ i, 0 < α i ∧ α i < 4) ∧
                  Q.map (algebraMap ℤ ℝ) =
                    (Polynomial.X - Polynomial.C (4 + δ)) *
                      ∏ i : Fin 27,
                        (Polynomial.X - Polynomial.C (α i)) ∧
                    51 ≤ polynomialTrace Q ∧
                      polynomialTrace Q ≤ 61 ∧
                        1 ≤ -Q.eval (4 : ℤ) ∧
                          -Q.eval (4 : ℤ) ≤ 12849

end

end MathlibPlus.Open.NumberTheory.Claim29530
