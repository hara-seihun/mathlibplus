import MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

namespace MathlibPlus.Open.ResearchFormalization.R2614Claim42806

open MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818
open scoped BigOperators

noncomputable section

abbrev Part := MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818.Part

def skippedOffsets {m : ℕ} : Fin m → ℤ :=
  fun j => if j.1 = 0 then (-1 : ℤ) else (j.1 : ℤ)

def precedingColumnMinor {m : ℕ} (R : ℕ) (p : Part m) : ℚ :=
  Matrix.det (fun i j =>
    if j.1 = 0 then
      (((R : ℚ) - 1) / (R : ℚ)) *
        rowUniformLaurentKernel R (rowCoordinate p i) (-1)
    else
      rowUniformLaurentKernel R (rowCoordinate p i) (j.1 : ℤ))

def rowAmplitude (d m : ℕ) (p : Part m) : ℚ :=
  kernelMinor (d - m + 1) (consecutiveOffsets m) p

def rowAmplitudeAfterBottomOne (d m : ℕ) (p : Part m) : ℚ :=
  kernelMinor (d - m) (consecutiveOffsets (m + 1)) (Fin.snoc p 1)

def skippedAmplitude (d m : ℕ) (p : Part m) : ℚ :=
  precedingColumnMinor (d - m + 1) p

def skippedFourAmplitude (R : ℕ) (p : Part 4) : ℚ :=
  kernelMinor R skippedFourOffsets p

/-- Claim 42806: the Laplace boundary identity retains the preceding Pascal
column, and at four rows its normalized skipped determinant is the genuine
(-1,1,2,3) minor giving the bottom-one boundary. -/
def claim42806 : Prop :=
  (∀ d m : ℕ, 2 ≤ m → m + 1 ≤ d →
    ∀ p : Part m, admissiblePartition d m p →
      ∀ x : Polynomial ℚ,
        let R := d - m + 1
        (x + Polynomial.C (R : ℚ)) *
              Polynomial.C (rowAmplitude d m p) -
            Polynomial.C (rowAmplitudeAfterBottomOne d m p) =
          x * Polynomial.C (rowAmplitude d m p) +
            Polynomial.C
                ((R : ℚ) / ((R - 1 : ℕ) : ℚ)) *
              Polynomial.C (skippedAmplitude d m p)) ∧
  (∀ d : ℕ, 5 ≤ d →
    ∀ p : Part 4, admissiblePartition d 4 p →
      let R := d - 3
      let G := skippedFourAmplitude R p
      let U := (2 * Polynomial.X) *
          Polynomial.C (nativeFourMinor d p) + Polynomial.C G
      U = fourToFiveBoundary d p ∧
        Polynomial.C G =
          Polynomial.C (R : ℚ) * Polynomial.C (nativeFourMinor d p) -
            Polynomial.C (nativeFiveMinor d (Fin.snoc p 1)))

end

end MathlibPlus.Open.ResearchFormalization.R2614Claim42806
