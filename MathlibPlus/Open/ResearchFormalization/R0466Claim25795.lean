import MathlibPlus.Open.ResearchFormalization.R0466BoydChambers

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0466

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796

/-- Claim 25795: the ordered trace-root/zero crossings have the universal
alternating sign law, and their upper-semicircle imaginary parts have the same
maximal-turn alternation. -/
def claim25795 : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ)
    (cstar qstar Astar : Polynomial ℝ)
    (u : Fin (n - 1) → ℝ) (S : Set (Fin n → ℝ)) (θstar : ℝ)
    (v : Fin n → ℝ),
    0 < n →
      (isSalemPolynomial R n ∧ traceLift R ell n) →
        affineBoydFormula (n := n) (traceToReal ell) cstar qstar Astar →
          coefficientVector cstar ∈ S →
            integralPolynomial cstar →
              pisotChamber n (traceToReal ell) S →
                exteriorRoot Astar θstar →
                  completeInteriorTraceRoots n (traceToReal ell) u →
                    (StrictMono v ∧
                      (∀ k : Fin n,
                        v k = 0 ∨ ∃ j : Fin (n - 1), v k = u j) ∧
                      (∀ x : ℝ,
                        (∃ k : Fin n, v k = x) ↔
                          (x = 0 ∨ ∃ j : Fin (n - 1), x = u j))) →
                      (∀ j : Fin n,
                        Real.sign (Polynomial.eval (v j) qstar) =
                          (-1 : ℝ) ^ (n - j.1)) ∧
                        (∀ j : Fin n, ∃ φ : ℝ,
                          0 < φ ∧ φ < Real.pi ∧
                            2 * Real.cos φ = v j ∧
                            Complex.re (phaseNormalized n φ Astar) = 0 ∧
                            Complex.im (phaseNormalized n φ Astar) ≠ 0 ∧
                            Real.sign
                                (Complex.im (phaseNormalized n φ Astar)) =
                              (-1 : ℝ) ^ (n - j.1)) ∧
                        (∀ φ : ℝ, 0 < φ → φ < Real.pi →
                          Complex.re (phaseNormalized n φ Astar) = 0 →
                            ∃ j : Fin n,
                              2 * Real.cos φ = v j ∧
                              Complex.im (phaseNormalized n φ Astar) ≠ 0 ∧
                              Real.sign
                                  (Complex.im (phaseNormalized n φ Astar)) =
                                (-1 : ℝ) ^ (n - j.1))

end MathlibPlus.Open.ResearchFormalization.R0466
