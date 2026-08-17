import Mathlib
import MathlibPlus.Analysis.ReciprocalXi

open Filter Set
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.NR2C0186Batch

noncomputable section

/-- The exact one-cutoff shadow-plus-leading-Dini model from C-0186. -/
noncomputable def oneCutoffProfile (P : Polynomial ℝ) (t : ℂ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi ((1 / 2 : ℂ) + Complex.I * t) /
      (2 * (Real.pi : ℂ)) *
    Complex.exp (-(0.015169226266280162 : ℂ) * t ^ 4) *
      (Polynomial.map (algebraMap ℝ ℂ) P).eval
        (t ^ 2 / (Real.sqrt 40 : ℂ)) -
    (690.225171612913413810019847006 : ℂ) /
      (2 * Complex.exp (100 : ℂ)) *
      (t * Complex.sin (40 * t) - (1 / 2 : ℂ) * Complex.cos (40 * t)) /
        (t ^ 2 + 1 / 4)

/-- The C-0185 degree-twelve profile used as `P₁` in C-0186. -/
noncomputable def pOne : Polynomial ℝ :=
    1 +
      Polynomial.C (-0.8824739608624199 : ℝ) * Polynomial.X +
      Polynomial.C (2.816598275979663 : ℝ) * Polynomial.X ^ 2 +
      Polynomial.C (-0.291823441775511462704736925086 : ℝ) * Polynomial.X ^ 7 +
      Polynomial.C (0.123027643379614215971149239916 : ℝ) * Polynomial.X ^ 8 +
      Polynomial.C (-0.0207839545323778109243242278602 : ℝ) * Polynomial.X ^ 9 +
      Polynomial.C (0.00175879823818437519844298958496 : ℝ) * Polynomial.X ^ 10 +
      Polynomial.C (-0.0000745504928632908194611477445219 : ℝ) * Polynomial.X ^ 11 +
      Polynomial.C (0.00000126611934386230650140945434773 : ℝ) * Polynomial.X ^ 12

/-- The exact second disjoint power block, supported in degrees 13 through 20. -/
noncomputable def pTwo : Polynomial ℝ :=
  pOne +
      Polynomial.C (-0.0000962868733179478142677130943071 : ℝ) * Polynomial.X ^ 13 +
      Polynomial.C (0.0000558820202091420720825640386391 : ℝ) * Polynomial.X ^ 14 +
      Polynomial.C (-0.0000139100370967417958365512517721 : ℝ) * Polynomial.X ^ 15 +
      Polynomial.C (0.00000192498664927043176019189284646 : ℝ) * Polynomial.X ^ 16 +
      Polynomial.C (-0.000000159947632046118214705947726983 : ℝ) * Polynomial.X ^ 17 +
      Polynomial.C (0.00000000797918354852525141626009891496 : ℝ) * Polynomial.X ^ 18 +
      Polynomial.C (-0.000000000221269934128117632858199186827 : ℝ) * Polynomial.X ^ 19 +
      Polynomial.C (0.00000000000263110981640649324429400415442 : ℝ) * Polynomial.X ^ 20

/-- The finite coefficient-root envelope, with the degree-zero coefficient excluded. -/
noncomputable def coefficientRootBound (P : Polynomial ℝ) : ℝ :=
  let positiveSupport := P.support.filter (fun j => 1 ≤ j)
  max 1 (if h : positiveSupport.Nonempty then
    positiveSupport.sup' h (fun j => Real.rpow |P.coeff j| (1 / (j : ℝ))) else 0)

/-- The exact maximum root of the eight newly added coefficients. -/
noncomputable def secondBlockRootBound : ℝ :=
  max
    (Real.rpow |pTwo.coeff 13 - pOne.coeff 13| (1 / (13 : ℝ)))
    (max
      (Real.rpow |pTwo.coeff 14 - pOne.coeff 14| (1 / (14 : ℝ)))
      (max
        (Real.rpow |pTwo.coeff 15 - pOne.coeff 15| (1 / (15 : ℝ)))
        (max
          (Real.rpow |pTwo.coeff 16 - pOne.coeff 16| (1 / (16 : ℝ)))
          (max
            (Real.rpow |pTwo.coeff 17 - pOne.coeff 17| (1 / (17 : ℝ)))
            (max
              (Real.rpow |pTwo.coeff 18 - pOne.coeff 18| (1 / (18 : ℝ)))
              (max
                (Real.rpow |pTwo.coeff 19 - pOne.coeff 19| (1 / (19 : ℝ)))
                (Real.rpow |pTwo.coeff 20 - pOne.coeff 20| (1 / (20 : ℝ)))))))))

/-- A positively oriented, closed rectangular boundary. -/
noncomputable def rectanglePath (a b c d : ℝ) (s : ℝ) : ℂ :=
  if s ≤ 1 / 4 then
    ((a + 4 * (b - a) * s : ℝ) : ℂ) + (c : ℂ) * Complex.I
  else if s ≤ 1 / 2 then
    (b : ℂ) + ((c + 4 * (d - c) * (s - 1 / 4) : ℝ) : ℂ) * Complex.I
  else if s ≤ 3 / 4 then
    ((b - 4 * (b - a) * (s - 1 / 2) : ℝ) : ℂ) + (d : ℂ) * Complex.I
  else
    (a : ℂ) + ((d - 4 * (d - c) * (s - 3 / 4) : ℝ) : ℂ) * Complex.I

/-- A direct winding-number certificate for the displayed boundary. -/
def windingCertificate (F : ℂ → ℂ) (a b c d : ℝ) (n : ℤ) : Prop :=
  let γ : ℝ → ℂ := rectanglePath a b c d
  ContinuousOn γ (Icc 0 1) ∧
    γ 0 = γ 1 ∧
    ContinuousOn (F ∘ γ) (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, F (γ s) ≠ 0) ∧
    ∃ θ : ℝ → ℝ,
      ContinuousOn θ (Icc 0 1) ∧
        (∀ s ∈ Icc (0 : ℝ) 1,
          Complex.exp (Complex.I * (θ s : ℂ)) =
            F (γ s) / ((‖F (γ s)‖ : ℝ) : ℂ)) ∧
        θ 1 - θ 0 = 2 * Real.pi * (n : ℝ)

/-- The certified strict modulus lower bound on a rectangular boundary. -/
def boundaryLowerBound (F : ℂ → ℂ) (a b c d bound : ℝ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1,
    bound < ‖F (rectanglePath a b c d s)‖

/-- The closed rectangle used for the zero-count assertions. -/
def rectangle (a b c d : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

/-- Local factorization with nonzero residual, used to count multiplicity. -/
def hasZeroMultiplicity (F : ℂ → ℂ) (z₀ : ℂ) (n : ℕ) : Prop :=
  ∃ g : ℂ → ℂ,
    ContinuousAt g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in nhds z₀, F z = (z - z₀) ^ n * g z

/-- A finite, explicitly enumerated zero set with its total multiplicity. -/
def countedZeroCertificate (F : ℂ → ℂ) (R : Set ℂ) (N : ℕ) : Prop :=
  ∃ (k : ℕ) (z : Fin k → ℂ) (mult : Fin k → ℕ),
    AnalyticOnNhd ℂ F R ∧
      (∀ i j : Fin k, z i = z j → i = j) ∧
      (∀ i : Fin k,
        z i ∈ R ∧ F (z i) = 0 ∧ 0 < mult i ∧
          hasZeroMultiplicity F (z i) (mult i)) ∧
      (∀ w : ℂ, w ∈ R → F w = 0 → ∃ i : Fin k, w = z i) ∧
      (∑ i : Fin k, mult i) = N

/-- Claim 2757: the one-cutoff shadow-plus-Dini model, with exact decimals. -/
def oneCutoffShadowPlusDiniModel_claim2757 : Prop :=
  ∀ (P : Polynomial ℝ) (t : ℂ),
    oneCutoffProfile P t =
      (MathlibPlus.Analysis.ReciprocalXi.xi ((1 / 2 : ℂ) + Complex.I * t) /
        (2 * (Real.pi : ℂ)) * Complex.exp
          (-(0.015169226266280162 : ℂ) * t ^ 4) *
      (Polynomial.map (algebraMap ℝ ℂ) P).eval
        (t ^ 2 / (Real.sqrt 40 : ℂ)) -
      (690.225171612913413810019847006 : ℂ) /
        (2 * Complex.exp (100 : ℂ)) *
      (t * Complex.sin (40 * t) - (1 / 2 : ℂ) * Complex.cos (40 * t)) /
        (t ^ 2 + 1 / 4))

/-- Claim 2759: the second block has the unchanged exact coefficient-root bound. -/
def unchangedCoefficientRootBound_claim2759 : Prop :=
  coefficientRootBound pTwo = coefficientRootBound pOne ∧
    coefficientRootBound pTwo = Real.sqrt (2.816598275979663 : ℝ) ∧
    (1.678272408156573 : ℝ) ≤ coefficientRootBound pTwo ∧
      coefficientRootBound pTwo < 1.678272408156574 ∧
    (∀ j : ℕ, 13 ≤ j → j ≤ 20 →
      Real.rpow |pTwo.coeff j - pOne.coeff j| (1 / (j : ℝ)) ≤
        secondBlockRootBound) ∧
    (0.4968596410657259 : ℝ) < secondBlockRootBound ∧
      secondBlockRootBound < 0.496859641065726

/-- Claim 2760: the earlier winding four becomes winding three with three counted zeros. -/
def packetWindingDropsToThree_claim2760 : Prop :=
  windingCertificate
      (oneCutoffProfile pOne)
      8.5 9.0 0.02 0.49 4 ∧
    windingCertificate
      (oneCutoffProfile pTwo)
      8.5 9.0 0.02 0.49 3 ∧
    boundaryLowerBound
      (oneCutoffProfile pTwo)
      8.5 9.0 0.02 0.49 (4.5446 * Real.rpow 10 (-43 : ℝ)) ∧
    countedZeroCertificate
      (oneCutoffProfile pTwo)
      (rectangle 8.5 9.0 0.02 0.49) 3

/-- Claim 2761: winding two and exactly two counted zeros in the symmetric box. -/
def symmetricBoxZeroCount_claim2761 : Prop :=
  windingCertificate
      (oneCutoffProfile pTwo)
      8.77 8.82 (-0.01) 0.01 2 ∧
    boundaryLowerBound
      (oneCutoffProfile pTwo)
      8.77 8.82 (-0.01) 0.01 (1.3622 * Real.rpow 10 (-42 : ℝ)) ∧
    countedZeroCertificate
      (oneCutoffProfile pTwo)
      (rectangle 8.77 8.82 (-0.01) 0.01) 2

end

end MathlibPlus.Open.Analysis.NR2C0186Batch
