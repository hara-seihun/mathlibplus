import MathlibPlus.Open.ResearchFormalization.BoydWeights25796
import MathlibPlus.Open.ResearchFormalization.BoydBudget25797
import MathlibPlus.Open.ResearchFormalization.LagrangeRatios25812

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BoydNormBudgetClaim25808

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796

/-- Claim 25808: weighted AM--GM gives the displayed norm-budget inequality
for every arbitrary integral correction in the anchor-defined same-chamber
sublevel, not only for the fixed anchor. -/
def normBudgetInequality_claim25808 : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ)
    (cstar qstar Astar : Polynomial ℝ)
    (u : Fin (n - 1) → ℝ) (S : Set (Fin n → ℝ))
    (θstar T : ℝ),
    (hn : 1 < n) →
      (isSalemPolynomial R n ∧ traceLift R ell n) →
        affineBoydFormula n (traceToReal ell) cstar qstar Astar →
          BoydWeights25796.coefficientVector cstar ∈ S ∧
            BoydWeights25796.integralPolynomial cstar ∧
            BoydWeights25796.pisotChamber n (traceToReal ell) S ∧
              BoydWeights25796.exteriorRoot Astar θstar →
                BoydWeights25796.completeInteriorTraceRoots
                  n (traceToReal ell) u →
                  BoydBudget25797.exteriorTraceRoot
                    (traceToReal ell) T →
                    let xstar := θstar + θstar⁻¹
                    let β := BoydWeights25796.simplexNodes u xstar
                    let L : Fin n → Polynomial ℝ :=
                      fun j => lagrangeBasis β j
                    let last :=
                      BoydWeights25796.lastIndex
                        (Nat.zero_lt_of_lt hn)
                    let d : Fin n → ℝ := fun j =>
                      if j = last then -1 else
                        Real.sign (Polynomial.eval (β j) cstar)
                    let h := Real.sign
                      (Polynomial.eval 0
                        (traceToReal ell -
                          (2 : Polynomial ℝ) * cstar))
                    let w : Fin n → ℝ := fun j =>
                      h * d j * Polynomial.eval 0 (L j)
                    let b :=
                      Polynomial.C (Polynomial.eval xstar cstar) * L last
                    let H := h *
                      (Polynomial.eval 0 (traceToReal ell) -
                        2 * Polynomial.eval 0 b)
                    (∀ j : Fin n, 0 < w j) ∧
                      h = Real.sign (Polynomial.eval 0 (traceToReal ell)) ∧
                        0 < H →
                      ∀ (cZ : Polynomial ℤ) (y : Fin n → ℝ),
                        let c := cZ.map (algebraMap ℤ ℝ)
                        let q :=
                          traceToReal ell - (2 : Polynomial ℝ) * c
                        let m := h * Polynomial.eval 0 q
                        let N := Int.natAbs (Polynomial.resultant ell cZ)
                        let cT := Polynomial.eval T c
                        let weightProduct : ℝ :=
                          ∏ i : Fin (n - 1),
                            w (LagrangeRatios25812.interiorIndex hn i)
                        (BoydWeights25796.integralPolynomial c ∧
                          cZ ≠ 0 ∧
                          BoydWeights25796.coefficientVector c ∈ S ∧
                          (∃ A : Polynomial ℝ, ∃ θ : ℝ,
                            affineBoydFormula n (traceToReal ell) c q A ∧
                              BoydWeights25796.exteriorRoot A θ ∧ θ ≤ θstar) ∧
                          (∀ j : Fin n, 0 ≤ y j) ∧
                          c = b +
                            ∑ j : Fin n, (d j * y j) • L j) →
                          H ≥
                            m +
                              2 * ((n - 1 : ℕ) : ℝ) *
                                Real.rpow
                                  ((N : ℝ) * weightProduct / |cT|)
                                  ((1 : ℝ) /
                                    ((n - 1 : ℕ) : ℝ))

end MathlibPlus.Open.ResearchFormalization.BoydNormBudgetClaim25808
