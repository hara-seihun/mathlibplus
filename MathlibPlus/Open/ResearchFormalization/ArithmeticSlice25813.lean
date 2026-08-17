import MathlibPlus.Open.ResearchFormalization.BoydBudget25797

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.ArithmeticSlice25813

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydBudget25797

/-- Claim 25813: the base Lagrange term has the displayed value at the
exterior trace root, and its normalized value is the closed-budget
cancellation. -/
def claim25813 : Prop :=
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
                completeInteriorTraceRoots n (traceToReal ell) u →
                  exteriorTraceRoot (traceToReal ell) T →
                    Polynomial.eval 0 (traceToReal ell) ≠ 0 →
                      let xstar := θstar + θstar⁻¹
                      let β := simplexNodes u xstar
                      let L : Fin n → Polynomial ℝ :=
                        fun j => lagrangeBasis β j
                      let last := lastIndex (Nat.zero_lt_of_lt hn)
                      let h := Real.sign
                        (Polynomial.eval 0
                          (traceToReal ell -
                            (2 : Polynomial ℝ) * cstar))
                      let b :=
                        Polynomial.C (Polynomial.eval xstar cstar) * L last
                      let H := h *
                        (Polynomial.eval 0 (traceToReal ell) -
                          2 * Polynomial.eval 0 b)
                      let a := |Polynomial.eval 0 (traceToReal ell)|
                      let K :=
                        T * Polynomial.eval T
                          (Polynomial.derivative (traceToReal ell)) / a
                      Polynomial.eval T b =
                          θstar * Polynomial.eval T
                            (Polynomial.derivative (traceToReal ell)) *
                            (xstar - T) / (θstar - θstar⁻¹) ∧
                        Polynomial.eval T b / K = (H - a) / 2

end

end MathlibPlus.Open.ResearchFormalization.ArithmeticSlice25813
