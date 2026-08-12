import Mathlib

noncomputable section

namespace MathlibPlus.Open.NumberTheory

/-- Registry statement for admitted claim 45425.  Mahler measure is the
standard complex Mahler measure of the coefficient-cast polynomial, and
Lehmer's number is defined from the displayed Lehmer polynomial.  The
reciprocity, constant-term, and inverse-root integrality conclusions are all
retained. -/
def claim45425_subLehmerCandidatesAreReciprocalUnits : Prop :=
  let L : Polynomial ℤ :=
    Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 - Polynomial.X ^ 6 -
      Polynomial.X ^ 5 - Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X + 1
  let tauL : ℝ := (L.map (Int.castRingHom ℂ)).mahlerMeasure
  ∀ (P : Polynomial ℤ),
    P.IsPrimitive →
    P.Monic →
    Irreducible P →
    (∀ n : ℕ, P ≠ Polynomial.cyclotomic n ℤ) →
    1 < (P.map (Int.castRingHom ℂ)).mahlerMeasure ∧
      (P.map (Int.castRingHom ℂ)).mahlerMeasure < tauL →
      P.reverse = P ∧
        P.constantCoeff = 1 ∧
          ∀ α : ℂ,
            (P.map (Int.castRingHom ℂ)).IsRoot α →
              IsIntegral ℤ α⁻¹

end MathlibPlus.Open.NumberTheory
