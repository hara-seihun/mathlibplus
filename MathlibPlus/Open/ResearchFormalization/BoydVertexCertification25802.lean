import MathlibPlus.Open.ResearchFormalization.BoydWeights25796
import MathlibPlus.Open.ResearchFormalization.BoydBudget25797
import MathlibPlus.Open.ResearchFormalization.LehmerMinimum25803

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BoydVertexCertification25802

open MathlibPlus.Open.ResearchFormalization

/-- The real correction represented by an integer coefficient vector. -/
def integerCorrection {n : ℕ} (v : Fin n → ℤ) : Polynomial ℝ :=
  ∑ i : Fin n, Polynomial.C (v i : ℝ) * Polynomial.X ^ i.1

/-- The integer points of the exact closed same-chamber Boyd sublevel. -/
def integerSublevel {n : ℕ}
    (ell : Polynomial ℝ) (S : Set (Fin n → ℝ)) (θstar : ℝ) :
    Set (Fin n → ℤ) :=
  {v |
    MathlibPlus.Open.ResearchFormalization.BoydWeights25796.coefficientVector
        (integerCorrection v) ∈
      MathlibPlus.Open.ResearchFormalization.BoydWeights25796.closedRootSublevel
        n ell S θstar}

/-- A finite integer coefficient box obtained from one target-dependent real
coordinate bound. -/
def integerCoefficientBox {n : ℕ} (B : ℝ) : Set (Fin n → ℤ) :=
  {v | ∀ i : Fin n, |(v i : ℝ)| ≤ B}

/-- The exact no-smaller-root test for one integer correction in the Boyd
family. -/
def noSmallerPisotRoot {n : ℕ}
    (ell : Polynomial ℝ) (v : Fin n → ℤ) (θstar : ℝ) : Prop :=
  ∀ (q A : Polynomial ℝ) (θ : ℝ),
    affineBoydFormula n ell (integerCorrection v) q A →
      MathlibPlus.Open.ResearchFormalization.BoydWeights25796.exteriorRoot A θ →
        θstar ≤ θ

/-- The vertex evaluations used by the finite certificate are evaluations of
 the actual correction polynomials represented by the simplex vertices. -/
def vertexEvaluation {n : ℕ}
    (vertices : Fin (n + 1) → Fin n → ℝ)
    (cstar : Polynomial ℝ) (xstar : ℝ) (k : Fin (n + 1)) : ℝ :=
  Polynomial.eval xstar
    (MathlibPlus.Open.ResearchFormalization.BoydWeights25796.correctionPolynomial
      (vertices k) - cstar)

/-- Checking the no-smaller-root condition on the exact integer sublevel is
 equivalent to checking its points in a containing finite box. -/
def finiteIntegerReplay {n : ℕ}
    (I box : Set (Fin n → ℤ)) (ell : Polynomial ℝ) (θstar : ℝ) : Prop :=
  (∀ v : Fin n → ℤ, v ∈ I → noSmallerPisotRoot ell v θstar) ↔
    (∀ v : Fin n → ℤ, v ∈ box → v ∈ I → noSmallerPisotRoot ell v θstar)

/-- Claim 25802: the degree-uniform Boyd simplex has its actual `n+1`
vertices, and its fixed-witness minimum-root check reduces to a finite
integer coefficient box.  The bound and the vertices are quantified after
that witness, so no numerical bound uniform in the degree or in the target is
asserted. -/
def claim25802 : Prop :=
  ∀ (n : ℕ) (R ell : Polynomial ℤ)
    (cstar qstar Astar : Polynomial ℝ)
    (u : Fin (n - 1) → ℝ) (S : Set (Fin n → ℝ)) (θstar : ℝ),
    (hn : 0 < n) →
      (isSalemPolynomial R n ∧ traceLift R ell n) →
        affineBoydFormula n (traceToReal ell) cstar qstar Astar →
          MathlibPlus.Open.ResearchFormalization.BoydWeights25796.coefficientVector
              cstar ∈ S ∧
            MathlibPlus.Open.ResearchFormalization.BoydWeights25796.integralPolynomial
              cstar ∧
            MathlibPlus.Open.ResearchFormalization.BoydWeights25796.pisotChamber
              n (traceToReal ell) S ∧
            MathlibPlus.Open.ResearchFormalization.BoydWeights25796.exteriorRoot
              Astar θstar →
              MathlibPlus.Open.ResearchFormalization.BoydWeights25796.completeInteriorTraceRoots
                n (traceToReal ell) u →
                let xstar := θstar + θstar⁻¹
                let β :=
                  MathlibPlus.Open.ResearchFormalization.BoydWeights25796.simplexNodes
                    u xstar
                let L : Fin n → Polynomial ℝ :=
                  fun j =>
                    MathlibPlus.Open.ResearchFormalization.lagrangeBasis β j
                let last :=
                  MathlibPlus.Open.ResearchFormalization.BoydWeights25796.lastIndex
                    hn
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
                let vertices :=
                  MathlibPlus.Open.ResearchFormalization.BoydWeights25796.simplexVertices
                    hn b L d w H
                let U :=
                  MathlibPlus.Open.ResearchFormalization.BoydWeights25796.closedRootSublevel
                    n (traceToReal ell) S θstar
                let I :=
                  integerSublevel (traceToReal ell) S θstar
                (MathlibPlus.Open.ResearchFormalization.BoydWeights25796.genuineBoundedSimplex
                    U vertices) ∧
                  ∃ B : ℝ,
                    0 ≤ B ∧
                      (∀ a : Fin n → ℝ, a ∈ U →
                        Finset.sum Finset.univ (fun i => |a i|) ≤ B) ∧
                      (∀ k : Fin (n + 1), ∀ i : Fin n,
                        |vertices k i| ≤ B) ∧
                      Set.Finite (integerCoefficientBox (n := n) B) ∧
                      I ⊆ integerCoefficientBox (n := n) B ∧
                      ((∀ v : Fin n → ℤ, v ∈ I →
                          noSmallerPisotRoot (traceToReal ell) v θstar) ↔
                        (∀ v : Fin n → ℤ,
                          v ∈ integerCoefficientBox (n := n) B → v ∈ I →
                            noSmallerPisotRoot (traceToReal ell) v θstar)) ∧
                      Set.Finite (Set.range
                        (vertexEvaluation vertices cstar xstar))

end MathlibPlus.Open.ResearchFormalization.BoydVertexCertification25802
