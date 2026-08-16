import Mathlib
import MathlibPlus.Algebra.Claim13230

noncomputable section

namespace MathlibPlus.Open.Algebra

/-- Claim 13231: reduction modulo 2 of the fixed degree-seven trace polynomial is
irreducible, and the same polynomial is irreducible over ℚ. -/
def claim13231_qModTwoIrreducibleAndQRationalIrreducible : Prop :=
  let q : Polynomial ℤ :=
    MathlibPlus.Algebra.Claim13230.degreeSevenTracePolynomial
  Irreducible (q.map (Int.castRingHom (ZMod 2))) ∧
    Irreducible (q.map (Int.castRingHom ℚ))

/-- Claim 13232: the roots of the fixed Q, counted by the root multiset, have
exactly the three stated open-interval counts. -/
def claim13232_qExactRealRootLocation : Prop :=
  let q : Polynomial ℝ :=
    MathlibPlus.Algebra.Claim13230.degreeSevenTracePolynomial.map
      (Int.castRingHom ℝ)
  Multiset.card (q.roots.filter (fun x => x < (-2 : ℝ))) = 1 ∧
    Multiset.card
        (q.roots.filter (fun x => (-2 : ℝ) < x ∧ x < (2 : ℝ))) = 6 ∧
      Multiset.card (q.roots.filter (fun x => (2 : ℝ) < x)) = 0

/-- Claim 13233: all seven roots of the fixed Q are real, expressed as its
real specialization having degree seven and splitting over ℝ. -/
def claim13233_qTotallyReal : Prop :=
  let q : Polynomial ℝ :=
    MathlibPlus.Algebra.Claim13230.degreeSevenTracePolynomial.map
      (Int.castRingHom ℝ)
  q.natDegree = 7 ∧ q.Splits

/-- Claim 13236: the fixed reciprocal-lift polynomial has the two stated
irreducible factor-degree patterns after reduction modulo 2 and modulo 7. -/
def claim13236_pModularFactorDegreePatterns : Prop :=
  let p : Polynomial ℤ := Polynomial.X ^ 14 - Polynomial.X ^ 12 +
    Polynomial.X ^ 7 - Polynomial.X ^ 2 + 1
  (∃ f g : Polynomial (ZMod 2),
      p.map (Int.castRingHom (ZMod 2)) = f * g ∧
        Irreducible f ∧ Irreducible g ∧ f.natDegree = 7 ∧ g.natDegree = 7) ∧
    (∃ f g : Polynomial (ZMod 7),
      p.map (Int.castRingHom (ZMod 7)) = f * g ∧
        Irreducible f ∧ Irreducible g ∧ f.natDegree = 2 ∧ g.natDegree = 12)

end MathlibPlus.Open.Algebra
