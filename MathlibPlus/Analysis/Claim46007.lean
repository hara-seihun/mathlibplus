import Mathlib

namespace MathlibPlus.Analysis.Claim46007

private abbrev TwoCube := Bool × Bool
private abbrev Policy := Fin 2

private def sign (b : Bool) : ℚ := if b then 1 else -1

private def g : TwoCube → ℚ := fun p => (sign p.1 + sign p.2) / 2

private def h : TwoCube → ℚ := fun _ => -1

private def mean (f : TwoCube → ℚ) : ℚ :=
  (f (false, false) + f (false, true) + f (true, false) + f (true, true)) / 4

private def variance (f : TwoCube → ℚ) : ℚ :=
  let m := mean f
  ((f (false, false) - m) ^ 2 +
    (f (false, true) - m) ^ 2 +
    (f (true, false) - m) ^ 2 +
    (f (true, true) - m) ^ 2) / 4

private def varianceAfterX (f : TwoCube → ℚ) (x : Bool) : ℚ :=
  let m := (f (x, false) + f (x, true)) / 2
  ((f (x, false) - m) ^ 2 + (f (x, true) - m) ^ 2) / 2

private def varianceAfterY (f : TwoCube → ℚ) (y : Bool) : ℚ :=
  let m := (f (false, y) + f (true, y)) / 2
  ((f (false, y) - m) ^ 2 + (f (true, y) - m) ^ 2) / 2

private def areaX (f : TwoCube → ℚ) : ℚ :=
  variance f + (varianceAfterX f false + varianceAfterX f true) / 2

private def areaY (f : TwoCube → ℚ) : ℚ :=
  variance f + (varianceAfterY f false + varianceAfterY f true) / 2

/-- The area of the complete two-coordinate policy whose first query is `p`. -/
private def policyArea (p : Policy) (f : TwoCube → ℚ) : ℚ :=
  if p = 0 then areaX f else areaY f

/-- Intrinsic area, minimized over the two complete nonrepeating policies. -/
private def intrinsicArea (f : TwoCube → ℚ) : ℚ :=
  min (policyArea 0 f) (policyArea 1 f)

/-- Whether the Boolean atom is already computable with no coordinate query. -/
private def computesWithoutQuery (k : TwoCube → ℚ) : Bool :=
  decide (k (false, false) = k (false, false) ∧
    k (false, true) = k (false, false) ∧
    k (true, false) = k (false, false) ∧
    k (true, true) = k (false, false))

/-- The zero cost of an immediately computable atom, on this finite model. -/
private def q (k : TwoCube → ℚ) : ℚ :=
  if computesWithoutQuery k then 0 else 1

/-- Best completion area after a zero-query computation of `k`. -/
private def completionArea (p : Policy) (k f : TwoCube → ℚ) : ℚ :=
  if computesWithoutQuery k then policyArea p f else 0

private def F (k f : TwoCube → ℚ) : ℚ :=
  min (completionArea 0 k f) (completionArea 1 k f)

private def covariance (f k : TwoCube → ℚ) : ℚ :=
  let mf := mean f
  let mk := mean k
  ((f (false, false) - mf) * (k (false, false) - mk) +
    (f (false, true) - mf) * (k (false, true) - mk) +
    (f (true, false) - mf) * (k (true, false) - mk) +
    (f (true, true) - mf) * (k (true, true) - mk)) / 4

/-- The concrete two-coordinate covariance-correction obstruction from claim 46007. -/
theorem pointwiseCovarianceCorrectionFailure_claim46007 :
    computesWithoutQuery h = true ∧
      q h = 0 ∧
      F h g = 3 / 4 ∧
      intrinsicArea g = 3 / 4 ∧
      covariance g (fun p => g p - h p) = 1 / 2 ∧
      q h + covariance g (fun p => g p - h p) = 1 / 2 ∧
      F h g - (q h + covariance g (fun p => g p - h p)) = 1 / 4 := by
  native_decide

end MathlibPlus.Analysis.Claim46007
