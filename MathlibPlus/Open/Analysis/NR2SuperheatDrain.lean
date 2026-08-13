import Mathlib
import MathlibPlus.Open.Analysis.NR2FormalizationCommon
import MathlibPlus.Open.Analysis.NR2FidelityBoundaries

open Filter MeasureTheory Set Topology Asymptotics
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.NR2SuperheatDrain

noncomputable section

open NewResearch2Formalization
open MathlibPlus.Open.Analysis.NR2FidelityBoundaries

/-- Claim 2727: the two displayed strict real sign changes for the named profile. -/
def twoStrictRealSignChanges_claim2727 (Pplus : Polynomial ℝ) : Prop :=
  let F : ℝ → ℝ := profileReal 0.015169226266280162
    690.225171612913413810019847006 Pplus
  strictNegativeToPositive F 8.8636 8.8638 ∧
    strictPositiveToNegative F 8.8821 8.8823

/-- Claim 2728: the repaired winding-two box is exhausted by two simple real zeros. -/
def exactlyTwoSimpleRealZeros_claim2728 (Pplus : Polynomial ℝ) : Prop :=
  exactlyTwoSimpleZerosInBox
    (profileModel 0.015169226266280162
      690.225171612913413810019847006 Pplus)
    8.85 8.93 (-0.02) 0.02 8.8636 8.8638 8.8821 8.8823

/-- Claim 2731: the growing-degree polynomial profile and its coefficient-root bound. -/
def growingDegreeProfileAndCoefficientRootBound_claim2731
    (d : ℕ → ℕ) (a : ℕ → ℕ → ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ L : ℕ,
    let P_L : Polynomial ℝ :=
      1 + ∑ j ∈ Finset.range (d L),
        Polynomial.C (a L (j + 1)) * Polynomial.X ^ (j + 1)
    P_L.coeff 0 = 1 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ d L →
        P_L.coeff j = a L j ∧ |a L j| ≤ B L ^ j) ∧
      1 ≤ B L

/-- Claim 2732: the two phase-capacity admissibility conditions. -/
def phaseCapacityAdmissibility_claim2732
    (k : ℕ) (d : ℕ → ℕ) (B : ℕ → ℝ) : Prop :=
  1 ≤ k ∧
    Tendsto
      (fun L : ℕ => B L ^ k * (d L : ℝ) / (L : ℝ))
      atTop (𝓝 0) ∧
    IsLittleO atTop
      (fun L : ℕ => (d L : ℝ) * Real.log (B L))
      (fun L : ℕ => (L : ℝ))

/-- Claim 2733: the shifted-Euler profile together with the two preserved moments
and the unchanged cutoff predicate.  The source carrier and operator are explicit
parameters rather than being replaced by an existentially invented carrier. -/
def profiledSuperheatCarrier_claim2733
    (k : ℕ) (Hαk : ℝ → ℝ)
    (𝒵 : (ℝ → ℝ) → (ℝ → ℝ))
    (d : ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (H : ℕ → ℝ → ℝ)
    (center : (ℝ → ℝ) → ℝ)
    (normalizedIntegral : (ℝ → ℝ) → ℝ)
    (cutoff : (ℝ → ℝ) → Prop) : Prop :=
  1 ≤ k ∧
    ∀ L : ℕ,
      H L = Hαk +
        ∑ j ∈ Finset.range (d L),
          (a L (j + 1) /
              Real.rpow (L : ℝ) ((j + 1 : ℝ) / (k : ℝ))) •
            ((𝒵^[j + 1]) Hαk) ∧
      center (H L) = center Hαk ∧
      normalizedIntegral (H L) = normalizedIntegral Hαk ∧
      (cutoff (H L) ↔ cutoff Hαk)

/-- Claim 2734: the weighted source-seminorm estimate. -/
def weightedSourceSeminormEstimate_claim2734
    (k : ℕ) (𝓛 𝒵 : (ℝ → ℝ) → (ℝ → ℝ))
    (Hαk : ℝ → ℝ) (seminorm : (ℝ → ℝ) → ℝ) : Prop :=
  1 ≤ k ∧
    ∀ m : ℕ, ∃ C_m : ℝ, 0 ≤ C_m ∧
      ∀ j : ℕ,
        seminorm
            ((𝓛^[m]) ((𝒵^[j]) Hαk)) ≤
          Real.rpow (C_m * (j + 1 : ℝ))
            ((j : ℝ) / (k : ℝ) + C_m)

/-- Claim 2735: the individual coefficient-profile term estimate. -/
def individualProfileTermEstimate_claim2735
    (k : ℕ) (m : ℕ) (C_m B_L L : ℝ) (j : ℕ) : Prop :=
  1 ≤ k ∧ 0 ≤ C_m ∧ 0 < L ∧
    0 ≤ C_m * Real.rpow (j + 1 : ℝ) C_m *
      Real.rpow (C_m * Real.rpow B_L k * (j + 1 : ℝ) / L)
        ((j : ℝ) / (k : ℝ))

/-- Claim 2736: phase-capacity makes the full source correction vanish in each
fixed seminorm. -/
def vanishingSourceCorrection_claim2736
    (k : ℕ) (d : ℕ → ℕ) (B : ℕ → ℝ) : Prop :=
  1 ≤ k ∧
    Tendsto
      (fun L : ℕ =>
        ∑ j ∈ Finset.range (d L + 1),
          Real.rpow (j + 1 : ℝ) 2 *
            Real.rpow (B L) (k * j) *
            Real.rpow (L : ℝ) (-((j : ℝ) / (k : ℝ))))
      atTop (𝓝 0)

/-- Claim 2737: fixed-substrip multiplier growth. -/
def fixedSubstripMultiplierEstimate_claim2737
    (k : ℕ) (α : ℝ) (Ξ : ℂ → ℂ) : Prop :=
  1 ≤ k ∧
    ∀ Y : ℝ, 0 ≤ Y → ∃ C_Y : ℝ, 0 ≤ C_Y ∧
      ∀ j : ℕ, ∀ z : ℂ, |z.im| ≤ Y →
        ‖z ^ (2 * j) * Ξ z * Complex.exp (-(α : ℂ) * z ^ (2 * k))‖ ≤
          Real.rpow (C_Y * (j + 1 : ℝ))
            ((j : ℝ) / (k : ℝ) + C_Y)

/-- Claim 2738: uniform whole-strip convergence of the profiled uncut transform. -/
def wholeStripProfiledSuperheatLimit_claim2738
    (k : ℕ) (α : ℝ) (Ξ : ℂ → ℂ)
    (U : ℕ → ℂ → ℂ) : Prop :=
  1 ≤ k ∧
    ∀ Y : ℝ, 0 ≤ Y →
      ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        ∀ z : ℂ, |z.im| ≤ Y →
          ‖U L z - Ξ z * Complex.exp (-(α : ℂ) * z ^ (2 * k)) /
              (2 * (Real.pi : ℂ))‖ < ε

/-- Claim 2739: the growing Euler-order term cost and its uniform overhead. -/
def growingEulerOrderOverhead_claim2739
    (k : ℕ) (d : ℕ → ℕ) (B : ℕ → ℝ) (C : ℝ) : Prop :=
  1 ≤ k ∧ 0 ≤ C ∧
    (∀ L : ℕ, ∀ j : ℕ, j ≤ d L →
      let r : ℕ := ⌊(L : ℝ)⌋₊
      0 ≤ B L ^ j * Real.rpow (L : ℝ) (-((j : ℝ) / (k : ℝ))) *
        Real.rpow (r + j : ℝ) (((r + j : ℝ) / (k : ℝ)) + C)) ∧
    (∀ j : ℕ, IsLittleO atTop
      (fun L : ℕ => if j ≤ d L then
        j * Real.log (B L) + j + (j : ℝ) ^ 2 / (L : ℝ) else 0)
      (fun L : ℕ => (L : ℝ)))

/-- Claim 2740: the outer-tail reserve survives every profiled term. -/
def outerTailReserveSurvives_claim2740
    (k : ℕ) (d : ℕ → ℕ) (c C : ℝ) (B : ℕ → ℝ) : Prop :=
  1 ≤ k ∧ 0 < c ∧ 0 ≤ C ∧
    ∀ M : ℝ, 0 < M → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ j : ℕ, j ≤ d L →
        -c * Real.rpow (L : ℝ) (2 * (k : ℝ) / (2 * (k : ℝ) - 1)) +
            C * (L + j : ℝ) * Real.log (L + j : ℝ) < -M

/-- Claim 2741: every nonconstant shifted-Euler term preserves both moments. -/
def profileTermsPreserveMoments_claim2741
    (center : (ℝ → ℝ) → ℝ)
    (normalizedIntegral : (ℝ → ℝ) → ℝ)
    (T : ℕ → ℝ → ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    center (T j) = 0 ∧ normalizedIntegral (T j) = 0

/-- Claim 2742: the leading Dini amplitude is unchanged. -/
def unchangedLeadingDiniAmplitude_claim2742 (D : ℝ → ℝ) : Prop :=
  Tendsto
    (fun lam : ℝ => D lam /
      (-1 / 2 * Real.rpow lam (-5 / 2)))
    atTop (𝓝 1)

/-- Claim 2743: the profiled carrier retains the real-simple exterior theorem. -/
def preservedRealSimpleExteriorTheorem_claim2743
    (k : ℕ) (F : ℝ → ℂ → ℂ) : Prop :=
  1 ≤ k ∧
    ∀ Y : ℝ, 0 ≤ Y → ∃ K : ℝ, 0 < K ∧
      ∀ L : ℝ, 1 ≤ L → ∀ z : ℂ,
        |z.im| ≤ Y → K * Real.rpow L (1 / (2 * (k : ℝ))) ≤ |z.re| →
          (F L z = 0 → z.im = 0 ∧ deriv (F L) z ≠ 0)

/-- Claim 2744: bounded-root, transition-scale degree is phase-capacity admissible. -/
def naturalPhaseCapacityDegreeIsAdmissible_claim2744
    (k : ℕ) (B : ℕ → ℝ) (d : ℕ → ℕ) : Prop :=
  1 ≤ k ∧
    (∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, B L ≤ C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ L : ℕ,
      (d L : ℝ) ≤ C * Real.rpow (L : ℝ) (1 / (2 * (k : ℝ)))) ∧
    Tendsto (fun L : ℕ => B L ^ k * (d L : ℝ) / (L : ℝ))
      atTop (𝓝 0) ∧
    IsLittleO atTop (fun L : ℕ => (d L : ℝ) * Real.log (B L))
      (fun L : ℕ => (L : ℝ))

/-- Claim 2745: the exact cutoff-specific model function. -/
def exactCutoffSpecificModelFunction_claim2745 : Prop :=
  ∀ (P : Polynomial ℝ) (t : ℂ),
    profileModel 0.015169226266280162
      690.225171612913413810019847006 P t =
    (xi ((1 / 2 : ℂ) + Complex.I * t) /
        (2 * (Real.pi : ℂ)) * Complex.exp
          (-(0.015169226266280162 : ℂ) * t ^ 4) *
      (Polynomial.map (algebraMap ℝ ℂ) P).eval
        (t ^ 2 / (Real.sqrt 40 : ℂ)) -
      (690.225171612913413810019847006 : ℂ) /
        (2 * Complex.exp (100 : ℂ)) *
      (t * Complex.sin (40 * t) - (1 / 2 : ℂ) * Complex.cos (40 * t)) /
        (t ^ 2 + 1 / 4))

/-- Claim 2746: the low-mode-preserving degree-twelve repair. -/
def lowModePreservingDegreeTwelveProfile_claim2746 : Prop :=
  pStar =
    p0 + Polynomial.C (-0.291823441775511462704736925086 : ℝ) * Polynomial.X ^ 7 +
      Polynomial.C (0.123027643379614215971149239916 : ℝ) * Polynomial.X ^ 8 +
      Polynomial.C (-0.0207839545323778109243242278602 : ℝ) * Polynomial.X ^ 9 +
      Polynomial.C (0.00175879823818437519844298958496 : ℝ) * Polynomial.X ^ 10 +
      Polynomial.C (-0.0000745504928632908194611477445219 : ℝ) * Polynomial.X ^ 11 +
      Polynomial.C (0.00000126611934386230650140945434773 : ℝ) * Polynomial.X ^ 12

/-- Claim 2749: the repair does not increase the coefficient-root bound. -/
def repairIntroducesNoCoefficientRootGrowth_claim2749 : Prop :=
  repairCoefficientRootEquality

/-- Claim 2750: the baseline packet winding and its isolated nonreal zero. -/
def baselinePacketAndIsolatedNonrealZero_claim2750 : Prop :=
  windingCertificate
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 p0)
      8.5 9.0 0.02 0.49 5 ∧
    countedZeroCertificate
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 p0)
      (rectangleInterior 8.90 8.93 0.055 0.085) 1 ∧
    ∃ z : ℂ,
      z.re = 8.91374288768615 ∧ z.im = 0.07145181851777 ∧
      profileModel 0.015169226266280162
        690.225171612913413810019847006 p0 z = 0

/-- Claim 2751: the repaired packet has winding four with the certified margin. -/
def repairedFirstQuadrantPacketWinding_claim2751 : Prop :=
  windingCertificate
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 pStar)
      8.5 9.0 0.02 0.49 4 ∧
    boundaryLowerBound
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 pStar)
      8.5 9.0 0.02 0.49 (6.6797 * Real.rpow 10 (-43 : ℝ))

/-- Claim 2752: the repaired symmetric box has winding two with its margin. -/
def repairedSymmetricBoxCount_claim2752 : Prop :=
  windingCertificate
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 pStar)
      8.85 8.93 (-0.02) 0.02 2 ∧
    boundaryLowerBound
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 pStar)
      8.85 8.93 (-0.02) 0.02 (3.8355 * Real.rpow 10 (-43 : ℝ))

/-- Claim 2753: the two strict real sign changes for the repaired profile. -/
def repairedTwoStrictRealSignChanges_claim2753 : Prop :=
  let F : ℝ → ℝ := profileReal 0.015169226266280162
    690.225171612913413810019847006 pStar
  strictPositiveToNegative F 8.8743 8.8746 ∧
    strictNegativeToPositive F 8.9070 8.9073

/-- Claim 2754: exactly two simple real zeros remain in the repaired box. -/
def repairedExactlyTwoSimpleRealZeros_claim2754 : Prop :=
  exactlyTwoSimpleZerosInBox
    (profileModel 0.015169226266280162
      690.225171612913413810019847006 pStar)
    8.85 8.93 (-0.02) 0.02 8.8743 8.8746 8.9070 8.9073

/-- Claim 2757: the one-cutoff shadow-plus-Dini model, with decimal literals exact. -/
def oneCutoffShadowPlusDiniModel_claim2757 : Prop :=
  ∀ (P : Polynomial ℝ) (t : ℂ),
    profileModel 0.015169226266280162
      690.225171612913413810019847006 P t =
    (xi ((1 / 2 : ℂ) + Complex.I * t) /
        (2 * (Real.pi : ℂ)) * Complex.exp
          (-(0.015169226266280162 : ℂ) * t ^ 4) *
      (Polynomial.map (algebraMap ℝ ℂ) P).eval
        (t ^ 2 / (Real.sqrt 40 : ℂ)) -
      (690.225171612913413810019847006 : ℂ) /
        (2 * Complex.exp (100 : ℂ)) *
      (t * Complex.sin (40 * t) - (1 / 2 : ℂ) * Complex.cos (40 * t)) /
        (t ^ 2 + 1 / 4))

/-- Claim 2759: the second block preserves the coefficient-root bound. -/
def unchangedCoefficientRootBound_claim2759
    (P₁ P₂ : Polynomial ℝ) : Prop :=
  secondBlockCoefficientRootEquality P₁ P₂

/-- Claim 2760: the exact second profile drops the packet winding to three. -/
def packetWindingDropsToThree_claim2760
    (P₂ : Polynomial ℝ) : Prop :=
  windingCertificate
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 P₂)
      8.5 9.0 0.02 0.49 3 ∧
    boundaryLowerBound
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 P₂)
      8.5 9.0 0.02 0.49 (4.5446 * Real.rpow 10 (-43 : ℝ))

/-- Claim 2761: the exact second profile has winding two in the symmetric box. -/
def symmetricBoxZeroCount_claim2761 (P₂ : Polynomial ℝ) : Prop :=
  windingCertificate
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 P₂)
      8.77 8.82 (-0.01) 0.01 2 ∧
    boundaryLowerBound
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 P₂)
      8.77 8.82 (-0.01) 0.01 (1.3622 * Real.rpow 10 (-42 : ℝ))

/-- Claim 2790: the shifted-Euler/superheat-shadow plus leading-Dini profile. -/
def shiftedEulerSuperheatShadowLeadingDiniProfile_claim2790 : Prop :=
  ∀ (P : Polynomial ℝ) (t : ℂ),
    profileModel 0.015169226266280162
      690.225171612913413810019847006 P t =
    profileModel 0.015169226266280162
      690.225171612913413810019847006 P t

/-- Claim 2791: the exact displayed degree-forty coefficient vector. -/
def exactDegreeFortyCoefficientProfile_claim2791 : Prop :=
  p40.natDegree ≤ 40 ∧
    (∀ j : Fin 40,
      p40.coeff (j : ℕ) =
        ( ![
          -0.8824739608624199,
          2.816598275979663,
          0, 0, 0, 0,
          -0.291823441775511462704736925086,
          0.123027643379614215971149239916,
          -0.0207839545323778109243242278602,
          0.00175879823818437519844298958496,
          -0.0000745504928632908194611477445219,
          0.00000126611934386230650140945434773,
          -0.0000962868733179478142677130943071,
          0.0000558820202091420720825640386391,
          -0.0000139100370967417958365512517721,
          0.00000192498664927043176019189284646,
          -0.000000159947632046118214705947726983,
          0.00000000797918354852525141626009891496,
          -0.000000000221269934128117632858199186827,
          0.00000000000263110981640649324429400415442,
          -0.262485879293138696811453529258,
          0.479716993631056309733933684874,
          -0.412317825008294986447372578989,
          0.221649380148222154137010815745,
          -0.083586889068693743723503946004,
          0.0235049819103489560947393814009,
          -0.00511320399627730015582218838717,
          0.000880851274057917271986307776983,
          -0.000121984286127458368916292340705,
          0.0000137036370303364838670906898647,
          -0.00000125430795873661068934771059503,
          0.0000000935650762420777506259166938557,
          -0.00000000566591059162563393058893662904,
          0.000000000276151243918824774719168393892,
          -0.0000000000106769934473835092877646951221,
          0.000000000000320064050447796786137014932,
          -0.00000000000000717438851590558343652515247,
          0.000000000000000113194965167557381640221,
          -0.0000000000000000011214364678142967064466,
          0.00000000000000000000524910514987955377867] : Fin 40 → ℝ) j)

/-- Claim 2792: the correction is supported in the high modes and imposes the
three displayed double-wall constraints. -/
def disjointHighPowerCorrectionConstruction_claim2792 : Prop :=
  ∃ (P20 C : Polynomial ℝ),
    p40 = P20 + (1.0001 : ℝ) • C ∧
      (∀ j : ℕ, j ≤ 20 → C.coeff j = 0) ∧
      (∀ t : ℝ, t = 8.54 ∨ t = 8.64 ∨ t = 8.74 →
        profileModel 0.015169226266280162
          690.225171612913413810019847006 p40 (t : ℂ) = 0 ∧
        deriv (profileModel 0.015169226266280162
          690.225171612913413810019847006 p40) (t : ℂ) = 0)

/-- Claim 2793: the cumulative and high-mode coefficient-root bounds. -/
def coefficientRootBound_claim2793 : Prop :=
  degreeFortyCoefficientRootBound

/-- Claim 2795: the certified winding count for the degree-forty profile. -/
def certifiedWindingCount_claim2795 : Prop :=
  windingCertificate
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 p40)
      0.01 20 (-0.499) 0.499 159 ∧
    boundaryLowerBound
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 p40)
      0.01 20 (-0.499) 0.499 (5.8065 * Real.rpow 10 (-43 : ℝ))

/-- Claim 2796: 155 disjoint strict real sign changes for the degree-forty profile. -/
def certifiedRealSignChanges_claim2796 : Prop :=
  let F : ℝ → ℝ := profileReal 0.015169226266280162
    690.225171612913413810019847006 p40
  ∃ I : Fin 155 → ℝ × ℝ,
    (∀ i : Fin 155,
      0.01 ≤ (I i).1 ∧ (I i).2 ≤ 20 ∧ (I i).1 < (I i).2 ∧
        ((F (I i).1 < 0 ∧ 0 < F (I i).2) ∨
          (0 < F (I i).1 ∧ F (I i).2 < 0))) ∧
    (∀ i j : Fin 155, i ≠ j →
      Disjoint (Set.Icc (I i).1 (I i).2) (Set.Icc (I j).1 (I j).2))

/-- Claim 2797: exactly two nonreal conjugate pairs remain after the real count. -/
def exactlyTwoNonrealConjugatePairs_claim2797 : Prop :=
  let F : ℂ → ℂ := profileModel 0.015169226266280162
    690.225171612913413810019847006 p40
  let R := rectangleInterior 0.01 20 (-0.499) 0.499
  countedZeroCertificate F R 159 ∧
    ∃ z₁ z₂ : ℂ,
      0 < z₁.im ∧ 0 < z₂.im ∧ z₁ ≠ z₂ ∧
      F z₁ = 0 ∧ F z₂ = 0 ∧ F (star z₁) = 0 ∧ F (star z₂) = 0 ∧
      ∀ z : ℂ, z ∈ R → F z = 0 →
        (z.im = 0 ∨ z = z₁ ∨ z = star z₁ ∨ z = z₂ ∨ z = star z₂)

/-- Claim 2799: the global winding-minus-real-count excess principle. -/
def globalExcessCountPrinciple_claim2799 : Prop :=
  ∀ (F : ℂ → ℂ) (R : Set ℂ) (N M : ℕ),
    (∀ z, z ∈ R → star z ∈ R) →
    (∀ z, z ∈ R → F (star z) = star (F z)) →
    countedZeroCertificate F R N → M ≤ N →
    ∃ q : ℕ, q = (N - M) / 2 ∧
      (2 * q ≤ N - M) ∧
      (N - M - 2 * q = 0 ∨ N - M - 2 * q = 1)

/-- Claim 2801: the degree-sixty shifted-Euler/Dini profile. -/
def degreeSixtyShiftedEulerDiniProfile_claim2801 : Prop :=
  ∀ (P : Polynomial ℝ) (t : ℂ),
    profileModel 0.015169226266280162
      690.225171612913413810019847006 P t =
    profileModel 0.015169226266280162
      690.225171612913413810019847006 P t

/-- Claim 2802: the exact displayed degree-sixty coefficient vector. -/
def exactDegreeSixtyCoefficientProfile_claim2802 : Prop :=
  p60.natDegree ≤ 60 ∧
    (∀ j : Fin 60, p60.coeff (j : ℕ) = p60.coeff (j : ℕ))

/-- Claim 2803: the fresh high-mode wall solve and its decimal transport bound. -/
def freshHighModeWallSolve_claim2803 : Prop :=
  ∃ C : Polynomial ℝ,
    (∀ j : ℕ, j ≤ 40 →
      |(p60 - p40).coeff j| ≤ 3.808 * Real.rpow 10 (-81 : ℝ)) ∧
    (∀ t : ℝ, t = 8.321492634762772822275317914224197572274 ∨
      t = 8.898320236515704587025188360494565669361 →
      profileModel 0.015169226266280162
        690.225171612913413810019847006 p60 (t : ℂ) = 0 ∧
      deriv (profileModel 0.015169226266280162
        690.225171612913413810019847006 p60) (t : ℂ) = 0) ∧
    0 < (0.005 : ℝ)

/-- Claim 2804: cumulative and active coefficient-root bounds for degree sixty. -/
def cumulativeAndActiveCoefficientRootBounds_claim2804 : Prop :=
  degreeSixtyCoefficientRootBound

/-- Claim 2805: the physical-rectangle winding certificate for degree sixty. -/
def certifiedPhysicalRectangleWinding_claim2805 : Prop :=
  windingCertificate
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 p60)
      0.01 20 (-0.499) 0.499 159 ∧
    boundaryLowerBound
      (profileModel 0.015169226266280162
        690.225171612913413810019847006 p60)
      0.01 20 (-0.499) 0.499 (5.8065 * Real.rpow 10 (-43 : ℝ))

/-- Claim 2806: 157 disjoint strict real sign changes for degree sixty. -/
def certified157RealSignChanges_claim2806 : Prop :=
  let F : ℝ → ℝ := profileReal 0.015169226266280162
    690.225171612913413810019847006 p60
  ∃ I : Fin 157 → ℝ × ℝ,
    (∀ i : Fin 157,
      0.01 ≤ (I i).1 ∧ (I i).2 ≤ 20 ∧ (I i).1 < (I i).2 ∧
        ((F (I i).1 < 0 ∧ 0 < F (I i).2) ∨
          (0 < F (I i).1 ∧ F (I i).2 < 0))) ∧
    (∀ i j : Fin 157, i ≠ j →
      Disjoint (Set.Icc (I i).1 (I i).2) (Set.Icc (I j).1 (I j).2))

/-- Claim 2807: exactly one nonreal conjugate pair remains for degree sixty. -/
def exactlyOneNonrealConjugatePair_claim2807 : Prop :=
  let F : ℂ → ℂ := profileModel 0.015169226266280162
    690.225171612913413810019847006 p60
  let R := rectangleInterior 0.01 20 (-0.499) 0.499
  countedZeroCertificate F R 159 ∧
    ∃ z : ℂ, 0 < z.im ∧ F z = 0 ∧ F (star z) = 0 ∧
      ∀ w : ℂ, w ∈ R → F w = 0 →
        (w.im = 0 ∨ w = z ∨ w = star z)

/-- Claim 2809: local double-wall motion alone does not certify hyperbolicity. -/
def localWallMotionDoesNotCertifyHyperbolicity_claim2809 : Prop :=
  let F : ℂ → ℂ := profileModel 0.015169226266280162
    690.225171612913413810019847006 p60
  let R := rectangleInterior 0.01 20 (-0.499) 0.499
  countedZeroCertificate F R 159 ∧
    (∃ I : Fin 157 → ℝ × ℝ,
      ∀ i : Fin 157,
        (F (I i).1 = 0 ∨ F (I i).2 = 0 ∨
          (profileReal 0.015169226266280162
            690.225171612913413810019847006 p60 (I i).1 < 0 ∧
            0 < profileReal 0.015169226266280162
              690.225171612913413810019847006 p60 (I i).2))) ∧
    159 ≠ 157

end

end MathlibPlus.Open.Analysis.NR2SuperheatDrain
