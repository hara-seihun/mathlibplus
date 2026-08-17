import MathlibPlus.Open.ResearchFormalization.BoydAffineBatch
import MathlibPlus.Open.ResearchFormalization.LagrangeSimplexBatch

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BoydBudget25797

/-- The coefficient vector of a real polynomial in degree-`n` coordinates. -/
def coefficientVector {n : ℕ} (p : Polynomial ℝ) : Fin n → ℝ :=
  fun i => p.coeff i.1

def correctionPolynomial {n : ℕ} (v : Fin n → ℝ) : Polynomial ℝ :=
  ∑ i : Fin n, Polynomial.C (v i) * Polynomial.X ^ i.1

def integralPolynomial (p : Polynomial ℝ) : Prop :=
  ∀ i : ℕ, ∃ a : ℤ, p.coeff i = (a : ℝ)

def exteriorRoot (p : Polynomial ℝ) (θ : ℝ) : Prop :=
  1 < θ ∧
    Polynomial.eval θ p = 0 ∧
      ∀ z : ℂ,
        evalRealComplex p z = 0 → 1 < ‖z‖ → z = (θ : ℂ)

def wallPredicate {n : ℕ} (ell : Polynomial ℝ) (v : Fin n → ℝ) : Prop :=
  (∃ u : ℝ,
    -2 < u ∧ u < 2 ∧ u ≠ 0 ∧
      Polynomial.eval u ell = 0 ∧
        Polynomial.eval u (correctionPolynomial v) = 0) ∨
    Polynomial.eval 0
      (ell - (2 : Polynomial ℝ) * correctionPolynomial v) = 0

def connectedComponent {n : ℕ}
    (ell : Polynomial ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  S ⊆ {v | ¬ wallPredicate ell v} ∧
    IsConnected S ∧
      ∀ T : Set (Fin n → ℝ),
        S ⊆ T → T ⊆ {v | ¬ wallPredicate ell v} → IsConnected T → T ⊆ S

def pisotChamber
    (n : ℕ) (ell : Polynomial ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  connectedComponent ell S ∧
    ∃ v ∈ S, ∃ q A : Polynomial ℝ, ∃ θ : ℝ,
      affineBoydFormula n ell (correctionPolynomial v) q A ∧
        exteriorRoot A θ

def completeInteriorTraceRoots
    (n : ℕ) (ell : Polynomial ℝ) (u : Fin (n - 1) → ℝ) : Prop :=
  StrictMono u ∧
    (∀ i : Fin (n - 1),
      -2 < u i ∧ u i < 2 ∧ u i ≠ 0 ∧ Polynomial.eval (u i) ell = 0) ∧
      (∀ x : ℝ,
        -2 < x → x < 2 → x ≠ 0 → Polynomial.eval x ell = 0 →
          ∃ i : Fin (n - 1), u i = x)

def lastIndex {n : ℕ} (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

def simplexNodes {n : ℕ}
    (u : Fin (n - 1) → ℝ) (x : ℝ) : Fin n → ℝ :=
  fun j => if h : j.1 < n - 1 then u ⟨j.1, h⟩ else x

/-- The exterior trace root is the unique real trace root above `2`. -/
def exteriorTraceRoot (ell : Polynomial ℝ) (T : ℝ) : Prop :=
  2 < T ∧ Polynomial.eval T ell = 0 ∧
    ∀ x : ℝ, 2 < x → Polynomial.eval x ell = 0 → x = T

/-- The supremum of the one-axis slice of the weighted simplex. -/
def axisIntercept (H : ℝ) (w : ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ 2 * w * r ≤ H}

def unsignedCoordinateSimplex {n : ℕ}
    (L : Fin n → Polynomial ℝ) (H : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ j : Fin n, 0 ≤ y j) ∧
    Finset.sum Finset.univ (fun j =>
      |Polynomial.eval 0 (L j)| * y j) ≤ H / 2}

/-- Claim 25797: the closed budget, its unsigned formula, and all axis
intercepts.  The final equality exposes that the budget and intercept data do
not contain the chamber signs. -/
def claim25797 : Prop :=
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
                  exteriorTraceRoot (traceToReal ell) T →
                    let xstar := θstar + θstar⁻¹
                    let sstar := θstar - θstar⁻¹
                    let β := simplexNodes u xstar
                    let L : Fin n → Polynomial ℝ :=
                      fun j => lagrangeBasis β j
                    let last := lastIndex hn
                    let h := Real.sign
                      (Polynomial.eval 0
                        (traceToReal ell - (2 : Polynomial ℝ) * cstar))
                    let b :=
                      Polynomial.C (Polynomial.eval xstar cstar) * L last
                    let H := h *
                      (Polynomial.eval 0 (traceToReal ell) -
                        2 * Polynomial.eval 0 b)
                    let a := |Polynomial.eval 0 (traceToReal ell)|
                    let unsignedH :=
                      a * xstar * (2 * θstar - T) / (T * sstar)
                    let unsignedSimplex :=
                      unsignedCoordinateSimplex L H
                    (∀ j : Fin n, 0 < |Polynomial.eval 0 (L j)|) ∧
                      0 < sstar ∧ 0 < H ∧
                        H = unsignedH ∧
                          (∀ j : Fin n,
                            axisIntercept H
                                |Polynomial.eval 0 (L j)| =
                              H / (2 * |Polynomial.eval 0 (L j)|)) ∧
                            unsignedSimplex =
                              unsignedCoordinateSimplex L unsignedH

end MathlibPlus.Open.ResearchFormalization.BoydBudget25797
