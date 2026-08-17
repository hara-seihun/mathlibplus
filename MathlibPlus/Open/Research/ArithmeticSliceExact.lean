import MathlibPlus.Open.ResearchFormalization.BoydWeights25796

open scoped BigOperators

namespace MathlibPlus.Open.Research.ArithmeticSliceExact

noncomputable section

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.ResearchFormalization.BoydWeights25796

private def integralCorrection (cZ : Polynomial ℤ) : Polynomial ℝ :=
  cZ.map (algebraMap ℤ ℝ)

private def qCorrection (ell : Polynomial ℤ) (c : Polynomial ℝ) : Polynomial ℝ :=
  traceToReal ell - (2 : Polynomial ℝ) * c

private def integerQCorrection (ell cZ : Polynomial ℤ) : Polynomial ℤ :=
  ell - (2 : ℤ) • cZ

private def integerSliceValue (ell cZ : Polynomial ℤ) (h : ℝ) : ℤ :=
  if h = 1 then
    Polynomial.eval 0 (integerQCorrection ell cZ)
  else
    -Polynomial.eval 0 (integerQCorrection ell cZ)

private def sliceSet (H : ℝ) (ell : Polynomial ℤ) : Set ℤ :=
  {m | 0 < m ∧ (m : ℝ) < H ∧
    Int.ModEq 2 m |Polynomial.eval 0 ell|}

/-- Integral corrections in the open same-chamber simplex have an integral
constant-term slice parameter of fixed parity, and only finitely many such
slices occur.  The fixed anchor and its complete interior-root data are kept
separate from the arbitrary integral correction. -/
def claim25805 : Prop :=
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
                      (h = 1 ∨ h = -1) ∧
                        0 < H →
                    (∀ cZ : Polynomial ℤ, ∀ y : Fin n → ℝ,
                      let c := integralCorrection cZ
                      let q := qCorrection ell c
                      integralPolynomial c ∧
                        coefficientVector c ∈ S ∧
                        (∃ A : Polynomial ℝ, ∃ θ : ℝ,
                          affineBoydFormula n (traceToReal ell) c q A ∧
                            exteriorRoot A θ ∧ θ ≤ θstar) ∧
                        (∀ j : Fin n, 0 ≤ y j) ∧
                        c = b +
                          ∑ j : Fin n, (d j * y j) • L j →
                      let mR := h * Polynomial.eval 0 q
                      ∃ m : ℤ,
                        m = integerSliceValue ell cZ h ∧
                          (m : ℝ) = mR ∧
                          mR = H -
                            2 * ∑ j : Fin n, w j * y j ∧
                          (0 : ℤ) < m ∧
                            (m : ℝ) < H ∧
                              Int.ModEq 2 m |Polynomial.eval 0 ell|) ∧
                    Set.Finite (sliceSet H ell)

end
end MathlibPlus.Open.Research.ArithmeticSliceExact
