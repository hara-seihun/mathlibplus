import MathlibPlus.Open.ResearchFormalization.BoydWeights25796
import MathlibPlus.Open.ResearchFormalization.BoydBudget25797

open scoped BigOperators

namespace MathlibPlus.Open.Research.ResultantNormExact

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796

private def integralCorrection (cZ : Polynomial ℤ) : Polynomial ℝ :=
  cZ.map (algebraMap ℤ ℝ)

private def qCorrection (ell : Polynomial ℤ) (c : Polynomial ℝ) : Polynomial ℝ :=
  traceToReal ell - (2 : Polynomial ℝ) * c

private def absoluteResultant (ell cZ : Polynomial ℤ) : ℕ :=
  Int.natAbs (Polynomial.resultant ell cZ)

/-- The resultant norm identity on the exact Salem/chamber/simplex carrier,
with the fixed anchor kept distinct from the arbitrary nonzero integral
correction. -/
def claim25806 : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ)
    (cstar qstar Astar : Polynomial ℝ)
    (u : Fin (n - 1) → ℝ) (S : Set (Fin n → ℝ))
    (θstar T : ℝ),
    (hn : 0 < n) →
      (isSalemPolynomial R n ∧ traceLift R ell n) →
        affineBoydFormula n (traceToReal ell) cstar qstar Astar →
          coefficientVector cstar ∈ S ∧ integralPolynomial cstar ∧
            pisotChamber n (traceToReal ell) S ∧
              exteriorRoot Astar θstar →
                completeInteriorTraceRoots n (traceToReal ell) u →
                  MathlibPlus.Open.ResearchFormalization.BoydBudget25797.exteriorTraceRoot
                    (traceToReal ell) T →
                    let xstar := θstar + θstar⁻¹
                    let β := simplexNodes u xstar
                    let L : Fin n → Polynomial ℝ :=
                      fun j => lagrangeBasis β j
                    let last := lastIndex hn
                    let d : Fin n → ℝ := fun j =>
                      if j = last then -1 else
                        Real.sign (Polynomial.eval (β j) cstar)
                    let h := Real.sign
                      (Polynomial.eval 0
                        (traceToReal ell - (2 : Polynomial ℝ) * cstar))
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
                      (∀ cZ : Polynomial ℤ, ∀ y : Fin n → ℝ,
                        let c := integralCorrection cZ
                        let q := qCorrection ell c
                        let N := absoluteResultant ell cZ
                        integralPolynomial c ∧
                          cZ ≠ 0 ∧
                          coefficientVector c ∈ S ∧
                          (∃ A : Polynomial ℝ, ∃ θ : ℝ,
                            affineBoydFormula n (traceToReal ell) c q A ∧
                              exteriorRoot A θ ∧ θ ≤ θstar) ∧
                          (∀ j : Fin n, 0 ≤ y j) ∧
                          c = b +
                            ∑ j : Fin n, (d j * y j) • L j →
                        1 ≤ N ∧
                          (N : ℝ) =
                            |Polynomial.eval T c| *
                              ∏ i : Fin (n - 1),
                                |Polynomial.eval (u i) c| ∧
                          (N : ℝ) =
                            |Polynomial.eval T c| *
                              ∏ i : Fin (n - 1),
                                y (interiorIndex hn i))

end
end MathlibPlus.Open.Research.ResultantNormExact
