import MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

namespace MathlibPlus.Open.ResearchFormalization.Claim42804

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818

noncomputable section

/-- The zero-outside-support binomial used by the normalized Pascal minor. -/
def normalizedBinomial42804 (n k : ℕ) : ℚ :=
  if k ≤ n then (Nat.choose n k : ℚ) else 0

/-- The bottom-to-top row coordinate `q_i=p_(m-1-i)+i`. -/
def bottomToTopCoordinate42804 {m : ℕ} (p : Part m) (i : Fin m) : ℕ :=
  p (Fin.rev i) + i.1

/-- The Pascal coefficient with both ordinary support inequalities retained. -/
def riordanBinomial42804 (R q s : ℕ) : ℚ :=
  if s ≤ q then normalizedBinomial42804 (R + s) (q - s) else 0

/-- The content-cleared normalized amplitude before its Riordan-kernel
identification.  Its row and column content factors remain explicit. -/
def contentClearedNormalizedAmplitude42804
    (d m : ℕ) (p : Part m) : ℚ :=
  let R := d - m + 1
  let q : Fin m → ℕ := fun i => bottomToTopCoordinate42804 p i
  (∏ i : Fin m, ((R + q i : ℕ) : ℚ)) /
      (∏ j : Fin m, ((R + j.1 : ℕ) : ℚ)) *
    Matrix.det (fun i j =>
      riordanBinomial42804 R (q i) j.1)

/-- Claim 42804: the content-cleared normalized length-`m` amplitude is the
maximal Riordan minor with bottom-to-top rows and the consecutive column
offsets, including the native five-row specialization. -/
def claim42804 : Prop :=
  (∀ (d m : ℕ) (p : Part m),
      admissiblePartition d m p →
        let R := d - m + 1
        let q : Fin m → ℤ := fun i => rowCoordinate p i
        contentClearedNormalizedAmplitude42804 d m p =
          Matrix.det (fun i j =>
            rowUniformLaurentKernel R (q i) (consecutiveOffsets m j))) ∧
    (∀ (d : ℕ) (p : Part 5),
      admissiblePartition d 5 p →
        contentClearedNormalizedAmplitude42804 d 5 p = nativeFiveMinor d p)

end

end MathlibPlus.Open.ResearchFormalization.Claim42804
