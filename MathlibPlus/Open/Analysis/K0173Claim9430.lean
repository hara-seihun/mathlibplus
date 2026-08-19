import MathlibPlus.NumberTheory.HardyZ

namespace MathlibPlus.Open.Analysis.K0173Claim9430

noncomputable section

open MathlibPlus.NumberTheory

/-- The real Hardy amplitude in the canonical Hardy-Z normalization. -/
def hardyRealZ9430 (t : ℝ) : ℝ :=
  (hardyZ t).re

/-- The Speiser boundary curve in the original t-coordinate. -/
def hardyBoundaryCurve9430 (t : ℝ) : ℂ :=
  ((deriv hardyTheta t * hardyRealZ9430 t : ℝ) : ℂ) +
    ((deriv hardyRealZ9430 t : ℝ) : ℂ) * Complex.I

/-- The second derivative of the real Hardy amplitude in the intrinsic theta
clock. -/
def thetaClockSecondDerivative9430 (t : ℝ) : ℝ :=
  ((deriv hardyTheta t) * deriv (deriv hardyRealZ9430) t -
      (deriv (deriv hardyTheta) t) * deriv hardyRealZ9430 t) /
    (deriv hardyTheta t) ^ 3

/-- The first Laguerre expression after changing from t to the theta clock. -/
def thetaClockLaguerre9430 (t : ℝ) : ℝ :=
  (deriv hardyRealZ9430 t / deriv hardyTheta t) ^ 2 -
    hardyRealZ9430 t * thetaClockSecondDerivative9430 t

/-- Claim 9430: the stationary-point theta-clock Laguerre identity, the
boundary-phase derivative, and its positive-theta-prime stationary sign trace. -/
def stationaryPointOrientationIdentity_claim9430 : Prop :=
  ∀ t : ℝ,
    deriv hardyTheta t ≠ 0 →
      hardyRealZ9430 t ≠ 0 →
        deriv hardyRealZ9430 t = 0 →
          thetaClockLaguerre9430 t =
              -hardyRealZ9430 t * deriv (deriv hardyRealZ9430) t /
                (deriv hardyTheta t) ^ 2 ∧
            deriv (fun u : ℝ => Complex.arg (hardyBoundaryCurve9430 u)) t =
              deriv (deriv hardyRealZ9430) t /
                (deriv hardyTheta t * hardyRealZ9430 t) ∧
              (0 < deriv hardyTheta t →
                (deriv (fun u : ℝ => Complex.arg (hardyBoundaryCurve9430 u)) t < 0 ↔
                  hardyRealZ9430 t * deriv (deriv hardyRealZ9430) t < 0))

end

end MathlibPlus.Open.Analysis.K0173Claim9430
