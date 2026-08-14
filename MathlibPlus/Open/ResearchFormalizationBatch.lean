import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable def gaussianHermiteCarrier (x : ℝ) : ℝ :=
  x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)

noncomputable def gaussianCarrier (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * x ^ 2)

noncomputable def tiltedProfile (lmbda : ℝ) (r : ℕ) (θ x : ℝ) : ℝ :=
  (1 - x ^ 2 / lmbda ^ 2) ^ (2 * r + 2) * Real.exp (-θ * x ^ 2 / lmbda ^ 2)

noncomputable def tiltedCorrection (lmbda : ℝ) (r : ℕ) (θ : ℝ) : ℝ :=
  (∫ x in (-lmbda)..lmbda, tiltedProfile lmbda r θ x * gaussianHermiteCarrier x) /
    (∫ x in (-lmbda)..lmbda, tiltedProfile lmbda r θ x * gaussianCarrier x)

noncomputable def tiltedSource (lmbda : ℝ) (r : ℕ) (θ x : ℝ) : ℝ :=
  if |x| ≤ lmbda then
    tiltedProfile lmbda r θ x *
      (gaussianHermiteCarrier x - tiltedCorrection lmbda r θ * gaussianCarrier x)
  else
    0

noncomputable def realL1 (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, |f x|

noncomputable def complexAbs (z : ℂ) : ℝ :=
  ‖z‖

/-- Claim 2426: the correction coefficient is uniform over the bounded-tilt,
logarithmic-order compact-source family. -/
def claim2426 : Prop :=
  ∀ (a b Θ : ℝ),
    0 < a → a ≤ b → 0 ≤ Θ →
      ∃ (C lmbda0 : ℝ),
        0 ≤ C ∧ 1 < lmbda0 ∧
          ∀ (lmbda : ℝ) (r : ℕ) (θ : ℝ),
            lmbda0 ≤ lmbda →
              a * Real.log lmbda ≤ (r : ℝ) →
                (r : ℝ) ≤ b * Real.log lmbda →
                  |θ| ≤ Θ →
                    |tiltedCorrection lmbda r θ +
                        3 * (2 * (r : ℝ) + 2 + θ) /
                          (2 * Real.pi ^ 2 * lmbda ^ 2)| ≤
                      C * (Real.log lmbda) ^ 2 / lmbda ^ 4

/-- Claim 2427: the source approximation and the tilt Lipschitz estimate are
uniform over the same family. -/
def claim2427 : Prop :=
  ∀ (a b Θ : ℝ),
    0 < a → a ≤ b → 0 ≤ Θ →
      ∃ (C lmbda0 : ℝ),
        0 ≤ C ∧ 1 < lmbda0 ∧
          ∀ (lmbda : ℝ) (r : ℕ) (θ θ' : ℝ),
            lmbda0 ≤ lmbda →
              a * Real.log lmbda ≤ (r : ℝ) →
                (r : ℝ) ≤ b * Real.log lmbda →
                  |θ| ≤ Θ →
                    |θ'| ≤ Θ →
                      realL1 (fun x => tiltedSource lmbda r θ x - gaussianHermiteCarrier x) ≤
                          C * Real.log lmbda / lmbda ^ 2 ∧
                        realL1 (fun x => tiltedSource lmbda r θ x - tiltedSource lmbda r θ' x) ≤
                          C * |θ - θ'| / lmbda ^ 2

noncomputable def chebyshevPolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 => 2 * Polynomial.X * chebyshevPolynomial (n + 1) - chebyshevPolynomial n

noncomputable def chebyshevLeft : ℝ := 64 / Real.pi ^ 2

noncomputable def chebyshevRight : ℝ := 100 / Real.pi ^ 2

noncomputable def chebyshevAffine (x : ℝ) : ℝ :=
  (2 * x - (chebyshevLeft + chebyshevRight)) /
    (chebyshevRight - chebyshevLeft)

noncomputable def chebyshevAffinePolynomial : Polynomial ℝ :=
  Polynomial.C (2 / (chebyshevRight - chebyshevLeft)) * Polynomial.X -
    Polynomial.C ((chebyshevLeft + chebyshevRight) /
      (chebyshevRight - chebyshevLeft))

noncomputable def chebyshevRescaling (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (chebyshevPolynomial n).eval (-41 / 9)) *
    (chebyshevPolynomial n).comp chebyshevAffinePolynomial

noncomputable def intervalSupNorm (M : Polynomial ℝ) : ℝ :=
  sSup {y : ℝ | ∃ x ∈ Set.Icc chebyshevLeft chebyshevRight, y = |M.eval x|}

/-- Claim 2575: the gamma--Dini phase interval is the stated interval. -/
def claim2575 : Prop :=
  ∀ (Y : ℝ),
    0 ≤ Y → Y ≤ 1 / 2 →
      let τY : ℝ := 4 / Real.pi * (5 / 2 - Y)
      τY ^ 2 ∈ Set.Icc (64 / Real.pi ^ 2) (100 / Real.pi ^ 2)

/-- Claim 2576: the sharp fixed-at-zero polynomial envelope is the normalized
affine Chebyshev rescaling. -/
def claim2576 : Prop :=
  ∀ (n : ℕ),
    (chebyshevRescaling n).natDegree ≤ n ∧
      (chebyshevRescaling n).eval 0 = 1 ∧
        (∀ M : Polynomial ℝ,
          M.natDegree ≤ n → M.eval 0 = 1 →
            intervalSupNorm (chebyshevRescaling n) ≤ intervalSupNorm M) ∧
          intervalSupNorm (chebyshevRescaling n) =
            1 / |(chebyshevPolynomial n).eval (41 / 9)| ∧
            chebyshevAffine 0 = -41 / 9 ∧
              |(chebyshevPolynomial n).eval (41 / 9)| =
                ((9 : ℝ) ^ n + ((9 : ℝ) ^ n)⁻¹) / 2

/-- Claim 2607: Montgomery--Vaughan's generalized Hilbert inequality. -/
def claim2607 : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (a : Fin n → ℂ),
    0 < δ →
      (∀ i j : Fin n, i ≠ j → δ ≤ |ω i - ω j|) →
        complexAbs
            (∑ i : Fin n, ∑ j : Fin n,
              if i ≠ j then
                a i * starRingEnd ℂ (a j) /
                  ((ω i - ω j : ℝ) : ℂ)
              else
                0) ≤
          Real.pi / δ * ∑ i : Fin n, (complexAbs (a i)) ^ 2

/-- Claim 2608: the cardinality-free interval frame bounds. -/
def claim2608 : Prop :=
  ∀ (n : ℕ) (δ T α : ℝ) (ω : Fin n → ℝ) (a : Fin n → ℂ),
    0 < δ → 0 < T →
      (∀ i j : Fin n, i ≠ j → δ ≤ |ω i - ω j|) →
        (T - 2 * Real.pi / δ) * ∑ i : Fin n, (complexAbs (a i)) ^ 2 ≤
            (∫ x in α..(α + T),
              (complexAbs
                (∑ i : Fin n,
                  a i * Complex.exp
                    (Complex.I * ((ω i : ℂ) * (x : ℂ))))) ^ 2) ∧
          (∫ x in α..(α + T),
              (complexAbs
                (∑ i : Fin n,
                  a i * Complex.exp
                    (Complex.I * ((ω i : ℂ) * (x : ℂ))))) ^ 2) ≤
            (T + 2 * Real.pi / δ) * ∑ i : Fin n, (complexAbs (a i)) ^ 2

end MathlibPlus.Open.ResearchFormalizationBatch
