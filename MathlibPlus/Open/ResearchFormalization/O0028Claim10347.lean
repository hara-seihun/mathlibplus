import MathlibPlus.Open.ResearchFormalization.BatchRadialIntertwiner

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0028Claim10347

open MathlibPlus.Open.ResearchFormalization.BatchRadialIntertwiner

noncomputable section

/-- Claim 10347: the complete finite-source radial form is the positive
continuum form minus the exact von Mangoldt compressed-shift source sum. -/
def completeFiniteSourceRadialContinuum_claim10347 : Prop :=
  ∀ (t : ℝ), 0 < t →
    ∀ f : L2Unit,
      radialAfull t f =
        radialAplus t f -
          (1 / 2) *
            ∑' n : {n : ℕ // 2 ≤ n},
              (ArithmeticFunction.vonMangoldt n.1 /
                  Real.sqrt (n.1 : ℝ)) *
                compressedShiftPairing
                  (t * Real.log (n.1 : ℝ) / 2) f

end

end MathlibPlus.Open.ResearchFormalization.O0028Claim10347
