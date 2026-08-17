import MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0502ReciprocalFreeBlocks25967

noncomputable section

abbrev Index :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.Index

abbrev Composition :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.Composition

abbrev reflectIndex :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.reflectIndex

abbrev SixCoordinate :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.SixCoordinate

abbrev sixCompressedRowSpan :=
  MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.sixCompressedRowSpan

/-- The coefficient block of subset size `r` for the six-factor product row. -/
def coefficientBlock (N r : ℕ)
    (μ : Composition 6 N) : Index N → ℚ :=
  fun t =>
    MathlibPlus.Open.Algebra.WeightedAlphabetSixClaim25976.blockSum
      (m := 6) (N := N) r
      (fun u => if u = t then (1 : ℚ) else 0) μ

/-- Claim 25967: fixed-total six-factor coefficient blocks are reciprocal in
sizes four/two and five/one, the triple block is self-reciprocal, and the
resulting three-block free span has the stated ambient dimension. -/
def claim25967 : Prop :=
  ∀ (N : ℕ),
    6 ≤ N →
      (∀ μ : Composition 6 N, ∀ t : Index N,
        coefficientBlock N 4 μ t =
            coefficientBlock N 2 μ (reflectIndex N t) ∧
          coefficientBlock N 5 μ t =
            coefficientBlock N 1 μ (reflectIndex N t) ∧
          coefficientBlock N 3 μ t =
            coefficientBlock N 3 μ (reflectIndex N t)) ∧
      Module.finrank ℚ (sixCompressedRowSpan N) =
        Module.finrank ℚ
          (MathlibPlus.Algebra.Claim6218.monomialSpan 6 N) ∧
      MathlibPlus.Algebra.Claim6218.D 6 N =
        Module.finrank ℚ (sixCompressedRowSpan N) ∧
      Module.finrank ℚ (SixCoordinate N → ℚ) =
        2 * N + N / 2 + 3

end

end MathlibPlus.Open.ResearchFormalization.R0502ReciprocalFreeBlocks25967
