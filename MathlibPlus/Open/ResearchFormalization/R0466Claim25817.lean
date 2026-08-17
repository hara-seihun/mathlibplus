import MathlibPlus.Open.ResearchFormalization.BoydWeights25796
import MathlibPlus.Open.ResearchFormalization.BoydBudget25797
import MathlibPlus.Open.ResearchFormalization.LagrangeRatios25812

namespace MathlibPlus.Open.ResearchFormalization.R0466Claim25817

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The scalar factor in the one-dimensional AM--GM envelope. -/
def scalarEnvelopeValue (n : ℕ) (δ η s : ℝ) : ℝ :=
  (s / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) * |δ + η * s|

/-- The supremum of one scalar branch on the slice interval. -/
def scalarMaximum (n : ℕ) (B δ η : ℝ) : ℝ :=
  sSup (scalarEnvelopeValue n δ η '' Set.Icc 0 B)

/-- The maximum of the two endpoint-slope branches in the claimed
one-dimensional envelope. -/
def envelopeValue (n : ℕ) (δ ηMin ηMax s : ℝ) : ℝ :=
  (s / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) *
    max |δ + ηMin * s| |δ + ηMax * s|

def envelopeMaximum (n : ℕ) (B δ ηMin ηMax : ℝ) : ℝ :=
  sSup (envelopeValue n δ ηMin ηMax '' Set.Icc 0 B)

/-- The extrema of the exact finite list of interior slopes. -/
def etaMinimum {n : ℕ} (η : Fin (n - 1) → ℝ) : ℝ :=
  sInf (Set.range η)

def etaMaximum {n : ℕ} (η : Fin (n - 1) → ℝ) : ℝ :=
  sSup (Set.range η)

/-- The only possible interior stationary point of a scalar branch. -/
def stationaryPoint (n : ℕ) (δ η : ℝ) : ℝ :=
  -(((n - 1 : ℕ) : ℝ) * δ) / ((n : ℝ) * η)

/-- A scalar branch attains its maximum at the endpoint or at the displayed
stationary point when that point lies in the slice interval. -/
def scalarMaximumAttained
    (n : ℕ) (B δ η : ℝ) : Prop :=
  ∃ s : ℝ,
    s ∈ Set.Icc 0 B ∧
      scalarEnvelopeValue n δ η s = scalarMaximum n B δ η ∧
        (s = B ∨
          (let s₀ := stationaryPoint n δ η
           0 ≤ s₀ ∧ s₀ ≤ B ∧ s = s₀))

/-- The fixed chamber anchor and its exact Salem/Boyd/Lagrange carriers. -/
def anchorData
    (n : ℕ) (R : Polynomial ℤ) (ell : Polynomial ℤ)
    (cstar qstar Astar : Polynomial ℝ)
    (u : Fin (n - 1) → ℝ) (S : Set (Fin n → ℝ))
    (θstar T : ℝ) : Prop :=
  (isSalemPolynomial R n ∧ traceLift R ell n) ∧
    affineBoydFormula n (traceToReal ell) cstar qstar Astar ∧
      MathlibPlus.Open.ResearchFormalization.BoydWeights25796.coefficientVector
          cstar ∈ S ∧
        MathlibPlus.Open.ResearchFormalization.BoydWeights25796.integralPolynomial
          cstar ∧
          MathlibPlus.Open.ResearchFormalization.BoydWeights25796.pisotChamber
            n (traceToReal ell) S ∧
            MathlibPlus.Open.ResearchFormalization.BoydWeights25796.exteriorRoot
              Astar θstar ∧
              MathlibPlus.Open.ResearchFormalization.BoydWeights25796.completeInteriorTraceRoots
                n (traceToReal ell) u ∧
                MathlibPlus.Open.ResearchFormalization.BoydBudget25797.exteriorTraceRoot
                  (traceToReal ell) T

/-- Claim 25817: after fixing the chamber anchor separately from the
arbitrary integral correction on a slice, the exact resultant norm obeys the
one-dimensional endpoint-slope envelope and each scalar branch has only the
stated endpoint or stationary-point maximizers. -/
def claim25817 : Prop :=
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
              0 ≤ zsum ∧ zsum ≤ B ∧
              N = K / zprod *
                |δ + Finset.sum Finset.univ (fun i => η i * z i)| *
                Finset.prod Finset.univ z →
            N ≤ K / zprod *
                envelopeMaximum n B δ (etaMinimum η) (etaMaximum η) ∧
              scalarMaximumAttained n B δ (etaMinimum η) ∧
              scalarMaximumAttained n B δ (etaMaximum η)

end
end MathlibPlus.Open.ResearchFormalization.R0466Claim25817
