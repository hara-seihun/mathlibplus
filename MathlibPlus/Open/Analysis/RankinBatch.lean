import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis.RankinBatch

/-- The scalar-weight Fourier ray used by the real local forms. -/
def realFourierRay (k : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  Real.rpow y (k / 2) * Real.exp (-2 * Real.pi * (n : ℝ) * y)

/-- The logarithmic derivative `L = y ∂_y` on a Fourier ray. -/
def realLogScaleDerivative (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y => y * deriv f y

/-- Mellin pairing on the positive real ray. -/
def realRankinMoment (s : ℝ) (n : ℕ) (u v : ℝ → ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), Real.rpow y (s - 2) * u y * v y

def realI00 (s k : ℝ) (n : ℕ) : ℝ :=
  realRankinMoment s n (realFourierRay k n) (realFourierRay k n)

def realI10 (s k : ℝ) (n : ℕ) : ℝ :=
  realRankinMoment s n (realLogScaleDerivative (realFourierRay k n))
    (realFourierRay k n)

def realI11 (s k : ℝ) (n : ℕ) : ℝ :=
  realRankinMoment s n (realLogScaleDerivative (realFourierRay k n))
    (realLogScaleDerivative (realFourierRay k n))

def realI20 (s k : ℝ) (n : ℕ) : ℝ :=
  realRankinMoment s n
    (realLogScaleDerivative (realLogScaleDerivative (realFourierRay k n)))
    (realFourierRay k n)

/-- The first-jet Gram matrix and geodesic Hessian matrix. -/
def realG1 (s k : ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![realI11 s k n, realI10 s k n; realI10 s k n, realI00 s k n]

def realH2 (s k : ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![realI20 s k n, realI10 s k n; realI10 s k n, realI00 s k n]

/-- Positive definiteness for a real two-dimensional quadratic form. -/
def positiveDefinite2 (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < dotProduct x (Matrix.mulVec M x)

/-- Congruence to `diag(1,-1)`, i.e. inertia `(one positive, one negative)`. -/
def inertiaOneOne (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
    Matrix.det P ≠ 0 ∧
      P.transpose * M * P = !![(1 : ℝ), 0; 0, -1]

/-- For real `α = s + k - 1 > 0`, the local Gram and geodesic forms have
positive-definite and `(1,1)` signatures, respectively. -/
def claim13442 : Prop :=
  ∀ (s k : ℝ) (n : ℕ),
    0 < k → 0 < n → 0 < s + k - 1 →
      positiveDefinite2 (realG1 s k n) ∧ inertiaOneOne (realH2 s k n)

/-- The same Fourier ray and logarithmic derivative over the complex Mellin
parameter. -/
def complexFourierRay (k : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (Real.rpow y (k / 2) : ℂ) *
    Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * (n : ℂ) * (y : ℂ)))

def complexLogScaleDerivative (f : ℝ → ℂ) : ℝ → ℂ :=
  fun y => (y : ℂ) * deriv f y

def complexRankinMoment (s : ℂ) (n : ℕ) (u v : ℝ → ℂ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ), Complex.cpow (y : ℂ) (s - 2) * u y * v y

def complexI00 (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  complexRankinMoment s n (complexFourierRay k n) (complexFourierRay k n)

def complexI10 (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  complexRankinMoment s n (complexLogScaleDerivative (complexFourierRay k n))
    (complexFourierRay k n)

def complexI20 (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  complexRankinMoment s n
    (complexLogScaleDerivative (complexLogScaleDerivative (complexFourierRay k n)))
    (complexFourierRay k n)

def pureRaisedTop (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  complexI20 s k n / complexI00 s k n + (k : ℂ) / 4

def pureRaisedSchurReserve (s : ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  pureRaisedTop s k n -
    (complexI10 s k n / complexI00 s k n) ^ 2

def geodesicSchurReserve (s : ℂ) (k : ℝ) : ℂ :=
  -(s + (k : ℂ) - 1) / 4

/-- Replacing the geodesic top entry by the pure two-step raised entry gives
`(1-s)/4`, rather than the geodesic/Hodge reserve. -/
def claim13454 : Prop :=
  ∀ (s : ℂ) (k : ℝ) (n : ℕ),
    0 < k → 0 < n → 0 < (s + (k : ℂ) - 1).re →
      pureRaisedSchurReserve s k n = (1 - s) / 4 ∧
        pureRaisedSchurReserve s k n ≠ geodesicSchurReserve s k

end MathlibPlus.Open.Analysis.RankinBatch
