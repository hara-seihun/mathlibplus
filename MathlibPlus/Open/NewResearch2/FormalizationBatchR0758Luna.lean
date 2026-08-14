import Mathlib

namespace MathlibPlus.Open.NewResearch2.FormalizationBatchR0758Luna

noncomputable section

private def oneExteriorRoots (δ : ℝ) (α : Fin 27 → ℝ) : Fin 28 → ℝ :=
  Fin.cases (4 + δ) (fun i => α i)

private def validOneExterior (δ : ℝ) (α : Fin 27 → ℝ) : Prop :=
  0 < δ ∧ δ < (27 : ℝ) / 1000 ∧
    ∀ i, 0 < α i ∧ α i < 4

private def newtonSum (roots : Fin 28 → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin 28, (roots i) ^ k

/-- Claim 24506: the displayed one-exterior degree-28 root configuration and
its first three Newton sums.  The endpoint is a separate `Fin` coordinate,
not an interior root folded into an unconstrained list. -/
def oneExteriorRootConfiguration_claim24506 : Prop :=
  ∃ (δ : ℝ) (α : Fin 27 → ℝ),
    validOneExterior δ α ∧
      let roots := oneExteriorRoots δ α
      let S := (4 + δ) + ∑ i : Fin 27, α i
      let p₂ := (4 + δ) ^ 2 + ∑ i : Fin 27, (α i) ^ 2
      let p₃ := (4 + δ) ^ 3 + ∑ i : Fin 27, (α i) ^ 3
      S = newtonSum roots 1 ∧
        p₂ = newtonSum roots 2 ∧
        p₃ = newtonSum roots 3

/-- Claim 24510: cubic interior-support lower bound on the relevant root
configuration, with the source's strict inequality and denominator retained. -/
def cubicInteriorSupportLowerBound_claim24510 : Prop :=
  ∀ (δ : ℝ) (α : Fin 27 → ℝ),
    validOneExterior δ α →
      let roots := oneExteriorRoots δ α
      let S := newtonSum roots 1
      let p₂ := newtonSum roots 2
      let p₃ := newtonSum roots 3
      p₃ > -16 * S + 8 * p₂ + (4 * S - p₂) ^ 2 / (S - 4)

private def integralCoefficients (Q : Polynomial ℝ) : Prop :=
  ∀ n, ∃ z : ℤ, Q.coeff n = (z : ℝ)

private def oneExteriorPolynomial (δ : ℝ) (α : Fin 27 → ℝ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C (4 + δ)) *
    ∏ i : Fin 27, (Polynomial.X - Polynomial.C (α i))

/-- Claim 24515: the isolated endpoint cut at `(S,p₂)=(57,205)` for a
monic integral one-exterior polynomial. -/
def isolatedEndpointCut_claim24515 : Prop :=
  ∀ (Q : Polynomial ℝ) (δ : ℝ) (α : Fin 27 → ℝ),
    validOneExterior δ α →
      Q.Monic ∧
        integralCoefficients Q ∧
        Q = oneExteriorPolynomial δ α ∧
        -Q.eval (4 : ℝ) > 0 ∧
        newtonSum (oneExteriorRoots δ α) 1 = 57 ∧
        newtonSum (oneExteriorRoots δ α) 2 = 205 →
      newtonSum (oneExteriorRoots δ α) 3 ≥ 739 ∧
        newtonSum (oneExteriorRoots δ α) 3 ≠ 738

/-- A retained-prefix family is indexed by the exact depth carrier.  Each
prefix at depth `d` has `d+1` coefficient slots; the numerical claim below
refers to the filtered trace-56 populations of this family. -/
private abbrev PrefixFamily :=
  ∀ d : Fin 7, Finset (Fin (d.val + 1) → ℤ)

private def traceCount (R : PrefixFamily) (d : Fin 7) (S : ℤ) : ℕ :=
  (R d).filter (fun p => decide (∑ i, p i = S)) |>.card

end

end MathlibPlus.Open.NewResearch2.FormalizationBatchR0758Luna
