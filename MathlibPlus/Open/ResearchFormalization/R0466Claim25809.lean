import MathlibPlus.Open.ResearchFormalization.R0466Claim25817
import MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0466Claim25809

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796
open MathlibPlus.Open.ResearchFormalization.R0466Claim25817

noncomputable section

/-- The inclusion of the four interior trace nodes into the five-node
Lagrange coordinate space. -/
def interiorFive (i : Fin 4) : Fin 5 :=
  ⟨i.1, Nat.lt_trans i.isLt (Nat.lt_succ_self 4)⟩

/-- The signed Lagrange budget attached to the fixed Lehmer anchor. -/
def lehmerBudget25809
    (ell : Polynomial ℤ) (cstar : Polynomial ℝ)
    (u : Fin 4 → ℝ) (θstar : ℝ) : ℝ :=
  let xstar := θstar + θstar⁻¹
  let β := simplexNodes u xstar
  let L : Fin 5 → Polynomial ℝ := fun j => lagrangeBasis β j
  let last : Fin 5 := Fin.last 4
  let h := Real.sign
    (Polynomial.eval 0
      (traceToReal ell - (2 : Polynomial ℝ) * cstar))
  let b := Polynomial.C (Polynomial.eval xstar cstar) * L last
  h * (Polynomial.eval 0 (traceToReal ell) -
    2 * Polynomial.eval 0 b)

/-- The continuous envelope used for a fixed arithmetic slice.  This is the
right-hand side of the reviewed fixed-slice envelope with the exact Lehmer
five-node carrier, before an integral point is selected. -/
def arithmeticEnvelope25809
    (ell : Polynomial ℤ) (cstar : Polynomial ℝ)
    (u : Fin 4 → ℝ) (θstar T : ℝ) (m : ℤ) : ℝ :=
  let xstar := θstar + θstar⁻¹
  let β := simplexNodes u xstar
  let L : Fin 5 → Polynomial ℝ := fun j => lagrangeBasis β j
  let last : Fin 5 := Fin.last 4
  let d : Fin 5 → ℝ := fun j =>
    if j = last then -1 else
      Real.sign (Polynomial.eval (β j) cstar)
  let h : ℝ := Real.sign
    (Polynomial.eval 0
      (traceToReal ell - (2 : Polynomial ℝ) * cstar))
  let w : Fin 5 → ℝ := fun j =>
    h * d j * Polynomial.eval 0 (L j)
  let H := lehmerBudget25809 ell cstar u θstar
  let a := |Polynomial.eval 0 (traceToReal ell)|
  let K := T * Polynomial.eval T
    (Polynomial.derivative (traceToReal ell)) / a
  let η : Fin 4 → ℝ := fun i =>
    T * (xstar - u i) / (xstar * (T - u i))
  let B : ℝ := (H - (m : ℝ)) / 2
  let δ : ℝ := ((m : ℝ) - a) / 2
  let zprod : ℝ :=
    Finset.prod Finset.univ (fun i : Fin 4 => w (interiorFive i))
  K / zprod * envelopeMaximum 5 B δ
    (etaMinimum (n := 5) η) (etaMaximum (n := 5) η)

/-- A point of the exact integer arithmetic slice, with all carriers used by
 the reviewed fixed-slice norm statement retained. -/
def lehmerArithmeticSliceMember25809
    (ell : Polynomial ℤ) (S : Set (Fin 5 → ℝ))
    (u : Fin 4 → ℝ) (θL T : ℝ)
    (cZ qZ AZ : Polynomial ℝ) (θZ : ℝ)
    (y : Fin 5 → ℝ) (m : ℤ) : Prop :=
  let cstar := LehmerMinimum25803.lehmerCorrection
  let xstar := θL + θL⁻¹
  let β := simplexNodes u xstar
  let L : Fin 5 → Polynomial ℝ := fun j => lagrangeBasis β j
  let last : Fin 5 := Fin.last 4
  let d : Fin 5 → ℝ := fun j =>
    if j = last then -1 else
      Real.sign (Polynomial.eval (β j) cstar)
  let h : ℝ := Real.sign
    (Polynomial.eval 0
      (traceToReal ell - (2 : Polynomial ℝ) * cstar))
  let w : Fin 5 → ℝ := fun j =>
    h * d j * Polynomial.eval 0 (L j)
  let b : Polynomial ℝ :=
    Polynomial.C (Polynomial.eval xstar cstar) * L last
  let H := lehmerBudget25809 ell cstar u θL
  let a := |Polynomial.eval 0 (traceToReal ell)|
  let K := T * Polynomial.eval T
    (Polynomial.derivative (traceToReal ell)) / a
  let η : Fin 4 → ℝ := fun i =>
    T * (xstar - u i) / (xstar * (T - u i))
  let z : Fin 4 → ℝ := fun i =>
    w (interiorFive i) * y (interiorFive i)
  let B : ℝ := (H - (m : ℝ)) / 2
  let δ : ℝ := ((m : ℝ) - a) / 2
  let zsum : ℝ := Finset.sum Finset.univ z
  let zprod : ℝ :=
    Finset.prod Finset.univ (fun i : Fin 4 => w (interiorFive i))
  let N : ℝ :=
    |Polynomial.resultant (traceToReal ell) cZ|
  coefficientVector cZ ∈ S ∧
      integralPolynomial cZ ∧
        degreeAtMost cZ 5 ∧
          cZ ≠ 0 ∧
            affineBoydFormula 5 (traceToReal ell) cZ qZ AZ ∧
              exteriorRoot AZ θZ ∧
                coefficientVector cZ ∈
                  closedRootSublevel 5 (traceToReal ell) S θL ∧
                  (∀ j : Fin 5, 0 ≤ y j) ∧
                    cZ = b +
                      ∑ j : Fin 5, (d j * y j) • L j ∧
                      (m : ℝ) = h * Polynomial.eval 0
                        (traceToReal ell -
                          (2 : Polynomial ℝ) * cZ) ∧
                      0 < (m : ℝ) ∧
                        (m : ℝ) < H ∧
                          m % 2 = (3 : ℤ) % 2 ∧
                            0 < K ∧
                              (∀ j : Fin 5, 0 < w j) ∧
                                (∀ i : Fin 4, 0 < η i) ∧
                                  0 ≤ zsum ∧
                                    zsum ≤ B ∧
                                      N = K / zprod *
                                        |δ + Finset.sum Finset.univ
                                          (fun i : Fin 4 => η i * z i)| *
                                          Finset.prod Finset.univ z

/-- Claim 25809: the Lehmer budget leaves exactly the odd slices `1, 3, 5`,
and the complete top slice is excluded by the continuous resultant envelope
and the positive integer norm of an integral correction. -/
def claim25809 : Prop :=
  ∃ (R ell : Polynomial ℤ) (S : Set (Fin 5 → ℝ))
    (qL A_L : Polynomial ℝ) (u : Fin 4 → ℝ)
    (θL T : ℝ),
    traceToReal ell = LehmerMinimum25803.lehmerTrace ∧
      ell.coeff 0 = 3 ∧
        anchorData 5 R ell LehmerMinimum25803.lehmerCorrection
          qL A_L u S θL T ∧
          LehmerMinimum25803.coefficientVector
              LehmerMinimum25803.lehmerCorrection ∈ S ∧
            LehmerMinimum25803.pisotBoydChamber
              LehmerMinimum25803.lehmerTrace S ∧
              let H := lehmerBudget25809 ell
                LehmerMinimum25803.lehmerCorrection u θL
              5 < H ∧
                H < 6 ∧
                  (∀ m : ℤ,
                    0 < (m : ℝ) →
                      (m : ℝ) < H →
                        m % 2 = (3 : ℤ) % 2 →
                          m = 1 ∨ m = 3 ∨ m = 5) ∧
                    (∀ m : ℤ,
                      0 < (m : ℝ) →
                        (m : ℝ) < H →
                          m % 2 = (3 : ℤ) % 2 →
                            m ≠ 5 → m = 1 ∨ m = 3) ∧
                    (2476 / 1000000 : ℝ) < 1 ∧
                      arithmeticEnvelope25809 ell
                          LehmerMinimum25803.lehmerCorrection
                          u θL T 5 <
                        (2476 / 1000000 : ℝ) ∧
                        (∀ (cZ qZ AZ : Polynomial ℝ) (θZ : ℝ)
                            (y : Fin 5 → ℝ),
                          lehmerArithmeticSliceMember25809
                              ell S u θL T cZ qZ AZ θZ y 5 →
                            let N : ℝ :=
                              |Polynomial.resultant (traceToReal ell) cZ|
                            N ≤ arithmeticEnvelope25809 ell
                              LehmerMinimum25803.lehmerCorrection
                              u θL T 5 ∧
                              N < (2476 / 1000000 : ℝ) ∧
                              (∃ k : ℕ, 1 ≤ k ∧ N = (k : ℝ)) ∧
                                False)

end

end MathlibPlus.Open.ResearchFormalization.R0466Claim25809
