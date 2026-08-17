import MathlibPlus.Open.ResearchFormalization.BoydWeights25796

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0466Claim25793

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796

/-- The coefficient-space form of the exact Lagrange simplex coordinates. -/
def simplexCoordinateRepresentation
    {n : ℕ} (ell : Polynomial ℝ) (S : Set (Fin n → ℝ))
    (θstar : ℝ) (L : Fin n → Polynomial ℝ)
    (d : Fin n → ℝ) (h : ℝ) (b : Polynomial ℝ) : Prop :=
  ∀ v : Fin n → ℝ,
    v ∈ closedRootSublevel n ell S θstar →
      ∃! y : Fin n → ℝ,
        (∀ j : Fin n, 0 ≤ y j) ∧
          (Finset.sum Finset.univ (fun j =>
            h * d j * Polynomial.eval 0 (L j) * y j) ≤
            h * (Polynomial.eval 0 ell - 2 * Polynomial.eval 0 b) / 2) ∧
          correctionPolynomial v =
            b + Finset.sum Finset.univ (fun j =>
              (d j * y j) • L j)

/-- Claim 25793: every point in the closed same-chamber Pisot sublevel has
    the unique signed Lagrange-coordinate expression and exact simplex budget. -/
def claim25793_lagrangeCoordinateSimplexRepresentation : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ)
    (cstar qstar Astar : Polynomial ℝ)
    (u : Fin (n - 1) → ℝ) (S : Set (Fin n → ℝ)) (θstar : ℝ),
    (hn : 0 < n) →
      (isSalemPolynomial R n ∧ traceLift R ell n) →
        affineBoydFormula n (traceToReal ell) cstar qstar Astar →
          coefficientVector cstar ∈ S ∧ integralPolynomial cstar ∧
            pisotChamber n (traceToReal ell) S ∧
              exteriorRoot Astar θstar →
                completeInteriorTraceRoots n (traceToReal ell) u →
                  let xstar := θstar + θstar⁻¹
                  let β := simplexNodes u xstar
                  let L : Fin n → Polynomial ℝ :=
                    fun j => lagrangeBasis β j
                  let last := lastIndex hn
                  let d : Fin n → ℝ :=
                    fun j =>
                      if j = last then -1 else
                        Real.sign (Polynomial.eval (β j) cstar)
                  let h := Real.sign
                    (Polynomial.eval 0
                      (traceToReal ell - (2 : Polynomial ℝ) * cstar))
                  let b :=
                    Polynomial.C (Polynomial.eval xstar cstar) * L last
                  simplexCoordinateRepresentation
                    (traceToReal ell) S θstar L d h b

end

end MathlibPlus.Open.ResearchFormalization.R0466Claim25793
