import MathlibPlus.Open.Analysis.FormalizationBatchO0267

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0267ColumnErrors

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

open Filter
open scoped BigOperators

open MathlibPlus.Open.Analysis.FormalizationBatch
open MathlibPlus.Open.Analysis.FormalizationBatchO0267

/-- The normalized exterior-Cauchy entry of the anchored evaluation map. -/
noncomputable def anchoredEntry (M : ℕ) (z : ℂ) (n : ℤ) : ℂ :=
  if exteriorInteger M n then
    normalizedRowFactor z /
      (Complex.ofReal Real.pi * (z - (n : ℂ)))
  else 0

/-- The anchored evaluation map on finitely supported exterior Shannon coordinates. -/
noncomputable def anchoredOperator (M N : ℕ) (nodes : Fin N → ℂ)
    (a : ℤ →₀ ℂ) : Fin N → ℂ :=
  fun j => a.sum (fun n u => anchoredEntry M (nodes j) n * u)

/-- A unit exterior Shannon coordinate. -/
noncomputable def exteriorCoordinateVector (n₀ : ℤ) : ℤ →₀ ℂ :=
  Finsupp.single n₀ 1

/-- The finite-support `ℓ²` norm in the exterior Shannon coordinates. -/
noncomputable def finiteL2Norm (a : ℤ →₀ ℂ) : ℝ :=
  Real.sqrt (∑ n ∈ a.support, ‖a n‖ ^ 2)

/-- The datum obtained from one exterior column of the anchored evaluation map. -/
noncomputable def exteriorColumnDatum
    (M N : ℕ) (nodes : Fin N → ℂ) (n₀ : ℤ) : Fin N → ℂ :=
  anchoredOperator M N nodes (exteriorCoordinateVector n₀)

/-- The norm of the datum in the finite evaluation space. -/
noncomputable def datumNorm {N : ℕ} (d : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ j : Fin N, ‖d j‖ ^ 2)

/-- The order-`r` normalized exterior denominator truncation. -/
noncomputable def exteriorExpansionTruncation
    (M : ℕ) (z : ℂ) (n : ℤ) (r : ℕ) : ℂ :=
  ∑ ell ∈ Finset.range r, exteriorExpansionSummand M z n ell
/-- The normalized row entry of the order-`r` remainder. -/
noncomputable def remainderEntry
    (M : ℕ) (z : ℂ) (n : ℤ) (r : ℕ) : ℂ :=
  if exteriorInteger M n then
    normalizedRowFactor z / (Complex.ofReal Real.pi) *
      exteriorExpansionRemainder M r z n
  else 0

/-- The row error is the `ℓ²` norm of the displayed denominator remainder row. -/
noncomputable def rowError (M : ℕ) (z : ℂ) (r : ℕ) : ℝ :=
  Real.sqrt (∑' n : ℤ, ‖remainderEntry M z n r‖ ^ 2)

/-- The Hilbert--Schmidt norm of the order-`r` remainder. -/
noncomputable def hilbertSchmidtError
    (M N : ℕ) (nodes : Fin N → ℂ) (r : ℕ) : ℝ :=
  Real.sqrt (∑ j : Fin N, rowError M (nodes j) r ^ 2)

/-- The action of the exact remainder matrix on an exterior coordinate sequence. -/
noncomputable def remainderApply
    (M N : ℕ) (nodes : Fin N → ℂ) (r : ℕ) (a : ℤ → ℂ) : Fin N → ℂ :=
  fun j => ∑' n : ℤ, remainderEntry M (nodes j) n r * a n

/-- A direct operator-norm bound on the exact remainder matrix over `ℓ²`. -/
def operatorErrorBound
    (M N : ℕ) (nodes : Fin N → ℂ) (r : ℕ) (B : ℝ) : Prop :=
  ∀ a : ℤ → ℂ,
    Summable (fun n : ℤ => ‖a n‖ ^ 2) →
      Real.sqrt (∑ j : Fin N, ‖remainderApply M N nodes r a j‖ ^ 2) ≤
        B * Real.sqrt (∑' n : ℤ, ‖a n‖ ^ 2)

/-- The central rectangle condition for the normalized evaluation nodes. -/
def centralNodes
    (M : ℕ) (rho : ℝ) (nodes : Fin N → ℂ) : Prop :=
  ∀ j : Fin N,
    ‖nodes j - Complex.ofReal (anchorCenter M)‖ ≤ rho * (M : ℝ)

/-- The exterior center-distance square sum. -/
noncomputable def exteriorCenterSquareSum (M : ℕ) : ℝ :=
  ∑' n : ℤ,
    if exteriorInteger M n then
      1 / |anchorCenter M - (n : ℝ)| ^ 2
    else 0

/-- Claim 15164: exterior square-sum and row/operator error estimates. -/
def claim15164 : Prop :=
  (∃ C : ℝ, 0 < C ∧
    ∀ᶠ M : ℕ in atTop,
      exteriorCenterSquareSum M ≤ C / (M : ℝ)) ∧
  (∀ rho C₀ : ℝ,
    0 ≤ rho → rho < 1 / 2 → 0 < C₀ →
      ∃ q C C₁ : ℝ,
        0 < q ∧ q < 1 ∧ 0 < C ∧ 0 < C₁ ∧
          ∀ᶠ M : ℕ in atTop,
            ∀ (N : ℕ) (nodes : Fin N → ℂ) (r : ℕ),
              centralNodes M rho nodes →
                (∀ j : Fin N,
                  rowError M (nodes j) r ≤
                    C * Real.sqrt ((1 + |(nodes j).im|) / (M : ℝ)) * q ^ r) ∧
                ((∀ j : Fin N, |(nodes j).im| ≤ C₀ * (M : ℝ)) →
                  hilbertSchmidtError M N nodes r ≤
                      C₁ * Real.sqrt (N : ℝ) * q ^ r ∧
                    operatorErrorBound M N nodes r
                      (C₁ * Real.sqrt (N : ℝ) * q ^ r)))

/-- Asymptotic comparability, used for the `≈` and `Θ` scales in the source. -/
def asympComparable (f g : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ L : ℕ in atTop,
      c * |g L| ≤ |f L| ∧ |f L| ≤ C * |g L|

/-- `N ≈ M` for two count sequences. -/
def countComparable (M N : ℕ → ℕ) : Prop :=
  asympComparable (fun L => (N L : ℝ)) (fun L => (M L : ℝ))

/-- `|z_j-n₀| ≈ M` uniformly over a train. -/
def columnDistanceComparable
    (M N : ℕ → ℕ) (nodes : ∀ L : ℕ, Fin (N L) → ℂ)
    (n₀ : ℕ → ℤ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ L : ℕ in atTop,
      ∀ j : Fin (N L),
        c * (M L : ℝ) ≤ ‖nodes L j - (n₀ L : ℂ)‖ ∧
          ‖nodes L j - (n₀ L : ℂ)‖ ≤ C * (M L : ℝ)

/-- A fixed central fraction of the scaled train. -/
def centralTrain
    (M N : ℕ → ℕ) (rho : ℝ)
    (nodes : ∀ L : ℕ, Fin (N L) → ℂ) : Prop :=
  0 ≤ rho ∧ rho < 1 / 2 ∧
    ∀ᶠ L : ℕ in atTop,
      centralNodes (M L) rho (nodes L)

/-- The height-floor meaning of `Im z_j ≫ log L`. -/
def logarithmicHeightFloor
    (N : ℕ → ℕ) (nodes : ∀ L : ℕ, Fin (N L) → ℂ) : Prop :=
  ∃ h : ℝ, 0 < h ∧
    ∀ᶠ L : ℕ in atTop,
      ∀ j : Fin (N L),
        h * Real.log (L : ℝ) ≤ (nodes L j).im

/-- The count scale supplied by the anti-Stokes specialization. -/
def antiStokesCountScale
    (k : ℕ) (R : ℕ → ℝ) (M : ℕ → ℕ) : Prop :=
  1 ≤ k ∧
    asympComparable R (fun L => Real.rpow (L : ℝ) (1 / (2 * (k : ℝ)))) ∧
    asympComparable (fun L => (M L : ℝ)) (fun L => (L : ℝ) * R L)

/-- The unit-normalized coherent datum and its exact preimage. -/
noncomputable def normalizedColumnDatum
    (M N : ℕ) (nodes : Fin N → ℂ) (n₀ : ℤ) : Fin N → ℂ :=
  fun j => ((datumNorm (exteriorColumnDatum M N nodes n₀))⁻¹ : ℂ) *
    exteriorColumnDatum M N nodes n₀ j

noncomputable def normalizedColumnPreimage
    (M N : ℕ) (nodes : Fin N → ℂ) (n₀ : ℤ) : ℤ →₀ ℂ :=
  ((datumNorm (exteriorColumnDatum M N nodes n₀))⁻¹ : ℂ) •
    exteriorCoordinateVector n₀

/-- Claim 15170: one exterior column gives a coherent polynomial-cost datum. -/
def claim15170 : Prop :=
  (∀ (M N : ℕ) (nodes : Fin N → ℂ) (n₀ : ℤ),
    exteriorInteger M n₀ →
      finiteL2Norm (exteriorCoordinateVector n₀) = 1 ∧
        (∀ j : Fin N,
          exteriorColumnDatum M N nodes n₀ j = anchoredEntry M (nodes j) n₀)) ∧
  (∀ (M N : ℕ → ℕ)
      (nodes : ∀ L : ℕ, Fin (N L) → ℂ)
      (n₀ : ℕ → ℤ) (rho : ℝ),
    centralTrain M N rho nodes →
      countComparable M N →
      columnDistanceComparable M N nodes n₀ →
      (∀ᶠ L : ℕ in atTop,
        exteriorInteger (M L) (n₀ L)) →
      (∀ᶠ L : ℕ in atTop,
        ∀ j : Fin (N L), 1 ≤ (nodes L j).im) →
      (∃ c : ℝ, 0 < c ∧
        ∀ᶠ L : ℕ in atTop,
          (datumNorm (exteriorColumnDatum (M L) (N L) (nodes L) (n₀ L))) ^ 2 ≥
              c * (∑ j : Fin (N L), (nodes L j).im) / (M L : ℝ) ^ 2 ∧
            exteriorColumnDatum (M L) (N L) (nodes L) (n₀ L) ≠ 0)) ∧
  (∀ (k : ℕ) (R : ℕ → ℝ) (M N : ℕ → ℕ)
      (nodes : ∀ L : ℕ, Fin (N L) → ℂ)
      (n₀ : ℕ → ℤ) (rho : ℝ),
    (antiStokesCountScale k R M) →
      countComparable M N →
      centralTrain M N rho nodes →
      columnDistanceComparable M N nodes n₀ →
      logarithmicHeightFloor N nodes →
      (∀ᶠ L : ℕ in atTop,
        exteriorInteger (M L) (n₀ L)) →
      (∃ C : ℝ, 0 < C ∧
        ∀ᶠ L : ℕ in atTop,
          datumNorm (exteriorColumnDatum (M L) (N L) (nodes L) (n₀ L)) ≠ 0 ∧
            datumNorm (exteriorColumnDatum (M L) (N L) (nodes L) (n₀ L))⁻¹ =
              finiteL2Norm
                (normalizedColumnPreimage (M L) (N L) (nodes L) (n₀ L)) ∧
            datumNorm
                (normalizedColumnDatum (M L) (N L) (nodes L) (n₀ L)) = 1 ∧
            anchoredOperator (M L) (N L) (nodes L)
                (normalizedColumnPreimage (M L) (N L) (nodes L) (n₀ L)) =
              normalizedColumnDatum (M L) (N L) (nodes L) (n₀ L) ∧
            finiteL2Norm
                (normalizedColumnPreimage (M L) (N L) (nodes L) (n₀ L)) ≤
              C * Real.sqrt ((M L : ℝ) / Real.log (L : ℝ))))

end

end MathlibPlus.Open.Analysis.FormalizationBatchO0267ColumnErrors
