import Mathlib

namespace MathlibPlus.Open.Research1500

open scoped Classical BigOperators

/-- Claim 37904.  Independence of the marker is represented by a scalar in the
fraction field multiplying every coefficient of `G` to give the corresponding
coefficient of `F`. -/
def coefficientRankCriterionForMarkerIndependentRatio_claim37904 : Prop :=
  ∀ (A : Type*) [CommRing A] [IsDomain A]
    (F G : Polynomial A),
    G ≠ 0 →
    ((∀ i j : ℕ,
        F.coeff i * G.coeff j - F.coeff j * G.coeff i = 0) ↔
      ∃ q : FractionRing A, ∀ i : ℕ,
        algebraMap A (FractionRing A) (F.coeff i) =
          q * algebraMap A (FractionRing A) (G.coeff i)) ∧
    ∀ i j : ℕ, G.coeff j ≠ 0 →
      ((∀ a b : ℕ,
          F.coeff a * G.coeff b - F.coeff b * G.coeff a = 0) →
        algebraMap A (FractionRing A) (F.coeff i) =
          (algebraMap A (FractionRing A) (F.coeff j) /
            algebraMap A (FractionRing A) (G.coeff j)) *
            algebraMap A (FractionRing A) (G.coeff i))

end MathlibPlus.Open.Research1500
