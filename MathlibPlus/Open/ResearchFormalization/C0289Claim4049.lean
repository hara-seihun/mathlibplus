import MathlibPlus.Open.Analysis.BesselKernelBounds

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0289Claim4049

open MathlibPlus.Analysis.BesselK

noncomputable section

/-- The exact finite centered channel from the admitted order-four-six
formalization, including its endpoint term. -/
noncomputable def finiteTransform (r : ℕ) (x T : ℝ) : ℝ :=
  (Finset.Icc 1 (Nat.floor (Real.exp T))).sum
      (fun (m : ℕ) =>
        if (m : ℝ) ≤ Real.exp T then
          (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) *
            centeredKernel r x (Real.log m)
        else 0) +
    centeredKernel (r + 1) x T

/-- Claim 4049: at admissible positive kernel arguments, and for the
order-defined finite transform, differentiating in `x` with `T` fixed moves
both channels to the next integer order. -/
def claim4049_exactDerivativeLadderAtFixedCutoff : Prop :=
  (∀ (r : ℕ) (x t : ℝ),
    0 < x → 0 < t →
      HasDerivAt (fun y : ℝ => centeredKernel r y t)
        (centeredKernel (r + 1) x t) x) ∧
    (∀ (r : ℕ) (x T : ℝ),
      1 ≤ r → 0 < x →
        HasDerivAt (fun y : ℝ => finiteTransform r y T)
          (finiteTransform (r + 1) x T) x)

end

end MathlibPlus.Open.ResearchFormalization.C0289Claim4049
