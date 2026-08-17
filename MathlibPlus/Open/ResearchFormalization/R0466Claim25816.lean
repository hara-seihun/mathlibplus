import MathlibPlus.Open.ResearchFormalization.R0466Claim25817

namespace MathlibPlus.Open.ResearchFormalization.R0466Claim25816

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.R0466Claim25817

noncomputable section

/-- Claim 25816: on the exact arithmetic slice of an integral correction, the
resultant norm is the displayed weighted fixed-slice expression.  The
correction and its norm are the reviewed polynomial carriers, rather than
independent scalar witnesses. -/
def claim25816 : Prop :=
  ∀ (n : ℕ) (R : Polynomial ℤ) (ell : Polynomial ℤ)
    (cstar qstar Astar : Polynomial ℝ)
    (u : Fin (n - 1) → ℝ) (S : Set (Fin n → ℝ))
    (θstar T : ℝ),
    (hn : 1 < n) →
      anchorData n R ell cstar qstar Astar u S θstar T →
        ∀ (cZ qZ AZ : Polynomial ℝ) (θZ : ℝ)
          (y : Fin n → ℝ) (m : ℤ),
          let xstar := θstar + θstar⁻¹
          let β :=
            MathlibPlus.Open.ResearchFormalization.BoydWeights25796.simplexNodes
              u xstar
          let L : Fin n → Polynomial ℝ :=
            fun j => lagrangeBasis β j
          let last :=
            MathlibPlus.Open.ResearchFormalization.BoydWeights25796.lastIndex
              (Nat.zero_lt_of_lt hn)
          let interior :=
            MathlibPlus.Open.ResearchFormalization.BoydWeights25796.interiorIndex
              (Nat.zero_lt_of_lt hn)
          let d : Fin n → ℝ := fun j =>
            if j = last then -1 else
              Real.sign (Polynomial.eval (β j) cstar)
          let h : ℝ :=
            Real.sign
              (Polynomial.eval 0
                (traceToReal ell - (2 : Polynomial ℝ) * cstar))
          let w : Fin n → ℝ := fun j =>
            h * d j * Polynomial.eval 0 (L j)
          let b : Polynomial ℝ :=
            Polynomial.C (Polynomial.eval xstar cstar) * L last
          let H : ℝ :=
            h * (Polynomial.eval 0 (traceToReal ell) -
              2 * Polynomial.eval 0 b)
          let a : ℝ := |Polynomial.eval 0 (traceToReal ell)|
          let K : ℝ :=
            T * Polynomial.eval T (Polynomial.derivative (traceToReal ell)) / a
          let η : Fin (n - 1) → ℝ := fun i =>
            T * (xstar - u i) / (xstar * (T - u i))
          let z : Fin (n - 1) → ℝ := fun i =>
            w (interior i) * y (interior i)
          let B : ℝ := (H - (m : ℝ)) / 2
          let δ : ℝ := ((m : ℝ) - a) / 2
          let zsum : ℝ := Finset.sum Finset.univ z
          let zprod : ℝ :=
            Finset.prod Finset.univ (fun i => w (interior i))
          let N : ℝ :=
            |Polynomial.resultant (traceToReal ell) cZ|
          (MathlibPlus.Open.ResearchFormalization.BoydWeights25796.coefficientVector
              cZ ∈ S) ∧
            MathlibPlus.Open.ResearchFormalization.BoydWeights25796.integralPolynomial
              cZ ∧
              degreeAtMost cZ n ∧
              cZ ≠ 0 ∧
              affineBoydFormula n (traceToReal ell) cZ qZ AZ ∧
              MathlibPlus.Open.ResearchFormalization.BoydWeights25796.exteriorRoot
                AZ θZ ∧
              MathlibPlus.Open.ResearchFormalization.BoydWeights25796.coefficientVector
                cZ ∈
                MathlibPlus.Open.ResearchFormalization.BoydWeights25796.closedRootSublevel
                  n (traceToReal ell) S θstar ∧
              (∀ j : Fin n, 0 ≤ y j) ∧
              cZ = b + ∑ j : Fin n, (d j * y j) • L j ∧
              (m : ℝ) =
                h * Polynomial.eval 0
                  (traceToReal ell - (2 : Polynomial ℝ) * cZ) ∧
              0 < (m : ℝ) ∧
              0 < K ∧
              (∀ j : Fin n, 0 < w j) ∧
              (∀ i : Fin (n - 1), 0 < η i) ∧
              0 ≤ zsum ∧ zsum ≤ B →
            Polynomial.eval T cZ =
                K * (δ + Finset.sum Finset.univ
                  (fun i => η i * z i)) ∧
              N = K / zprod *
                |δ + Finset.sum Finset.univ (fun i => η i * z i)| *
                  Finset.prod Finset.univ z ∧
              ((a ≤ (m : ℝ)) →
                0 < Polynomial.eval T cZ ∧
                  |Polynomial.eval T cZ| = Polynomial.eval T cZ) ∧
              (Polynomial.eval T cZ = 0 → (m : ℝ) < a)

end

end MathlibPlus.Open.ResearchFormalization.R0466Claim25816
