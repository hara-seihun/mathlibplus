import MathlibPlus.Open.Basic

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Claim 856: the shifted polynomial/product transfer identity for a
positive-leading polynomial presented by its finite nonnegative-root
factorization.  The determinant conventions are inlined: a negative
consecutive derivative order contributes zero. -/
noncomputable def claim856_shiftProductTransfer : Prop :=
  ∀ (N : ℕ) (r : Fin N → ℝ) (c : ℝ),
    0 < c →
    (∀ i, 0 ≤ r i) →
    let f : Polynomial ℝ :=
      Polynomial.C c * ∏ i : Fin N,
        (Polynomial.X + Polynomial.C (r i))
    let h5 : Polynomial ℝ → ℝ → ℝ :=
      fun p x => Matrix.det (fun i j : Fin 5 =>
        ((Polynomial.derivative^[i.1 + j.1]) p).eval x)
    let d5 : Polynomial ℝ → ℝ :=
      fun p => Matrix.det (fun i j : Fin 5 =>
        if i.1 ≤ 4 + j.1 then
          ((Polynomial.derivative^[4 + j.1 - i.1]) p).eval 0
        else 0)
    (∀ x z : ℝ, 0 < x →
      f.eval (x + z) / f.eval x =
        ∏ i : Fin N, (1 + z / (x + r i))) ∧
      (∀ x : ℝ, 0 < x →
        h5 f x = (f.eval x) ^ 5 *
          d5 (f.comp (Polynomial.X + Polynomial.C x) *
            Polynomial.C (f.eval x)⁻¹))

/-- Claim 857: the order-five consecutive-derivative determinant is
nonnegative through degree seven under the stated real nonpositive-root
hypothesis. -/
noncomputable def claim857_globalDegreeAtMostSevenPositivity : Prop :=
  ∀ (f : Polynomial ℝ),
    f ≠ 0 →
    0 < f.leadingCoeff →
    f.natDegree ≤ 7 →
    (∀ z : ℂ,
      (Polynomial.map (algebraMap ℝ ℂ) f).IsRoot z →
        ∃ y : ℝ, y ≤ 0 ∧ z = (y : ℂ)) →
    ∀ x : ℝ, 0 ≤ x →
      0 ≤ Matrix.det (fun i j : Fin 5 =>
        ((Polynomial.derivative^[i.1 + j.1]) f).eval x)

end MathlibPlus.Open.Analysis
