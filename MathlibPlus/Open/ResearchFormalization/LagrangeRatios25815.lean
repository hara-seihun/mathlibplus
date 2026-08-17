import MathlibPlus.Open.ResearchFormalization.LagrangeRatios25812

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.LagrangeRatios25815

open MathlibPlus.Open.ResearchFormalization.LagrangeRatios25812

/-- The normalized target slope supplied by the fixed-slice exterior-evaluation
normal form. -/
def targetSlope (xstar T u : ℝ) : ℝ :=
  T * (xstar - u) / (xstar * (T - u))

/-- Positivity, the actual derivative, and the resulting order of the target
slopes on the exact Boyd/Lagrange carrier.  The terminal sub-Lehmer condition
is represented by the reviewed equivalent condition `xstar > T`. -/
def positivityAndMonotonicityOfTargetSlopes_claim25815 : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ)
    (cstar qstar Astar : Polynomial ℝ)
    (u : Fin (n - 1) → ℝ) (S : Set (Fin n → ℝ))
    (θstar T : ℝ),
    (hn : 1 < n) →
      (isSalemPolynomial R n ∧ traceLift R ell n) →
        affineBoydFormula n (traceToReal ell) cstar qstar Astar →
          coefficientVector cstar ∈ S ∧ integralPolynomial cstar ∧
            pisotChamber n (traceToReal ell) S ∧
              exteriorRoot Astar θstar →
                completeInteriorTraceRoots (n := n) (traceToReal ell) u →
                  exteriorTraceRoot (traceToReal ell) T →
                    Polynomial.eval 0 (traceToReal ell) ≠ 0 →
                      let xstar := θstar + θstar⁻¹
                      (∀ i : Fin (n - 1),
                        0 < targetSlope xstar T (u i) ∧
                        HasDerivAt
                          (fun v : ℝ => targetSlope xstar T v)
                          (T * (xstar - T) /
                            (xstar * (T - u i) ^ 2)) (u i)) ∧
                        (∀ i j : Fin (n - 1), i < j → xstar > T →
                          targetSlope xstar T (u i) <
                            targetSlope xstar T (u j)) ∧
                        (∀ i j : Fin (n - 1), i < j → xstar < T →
                          targetSlope xstar T (u j) <
                            targetSlope xstar T (u i)) ∧
                        (xstar > T →
                          StrictMono (fun i : Fin (n - 1) =>
                            targetSlope xstar T (u i)))

end MathlibPlus.Open.ResearchFormalization.LagrangeRatios25815
