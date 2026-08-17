import MathlibPlus.Open.ResearchFormalization.BoydAffineBatch
import MathlibPlus.Open.ResearchFormalization.LagrangeSimplexBatch

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BoydWeights25796

/-- The coefficient vector of a real polynomial in the degree-`n` monomial
coordinate space. -/
def coefficientVector {n : ℕ} (p : Polynomial ℝ) : Fin n → ℝ :=
  fun i => p.coeff i.1

/-- The correction polynomial represented by a finite coefficient vector. -/
def correctionPolynomial {n : ℕ} (v : Fin n → ℝ) : Polynomial ℝ :=
  ∑ i : Fin n, Polynomial.C (v i) * Polynomial.X ^ i.1

/-- Integrality of every coefficient of a real correction polynomial. -/
def integralPolynomial (p : Polynomial ℝ) : Prop :=
  ∀ i : ℕ, ∃ a : ℤ, p.coeff i = (a : ℝ)

/-- A unique real root outside the unit circle, with the exterior root written
as a positive real number. -/
def exteriorRoot (p : Polynomial ℝ) (θ : ℝ) : Prop :=
  1 < θ ∧
    Polynomial.eval θ p = 0 ∧
      ∀ z : ℂ,
        evalRealComplex p z = 0 → 1 < ‖z‖ → z = (θ : ℂ)

/-- A polynomial member together with the affine Boyd formula that defines it. -/
def boydMemberFormula {n : ℕ}
    (ell c A : Polynomial ℝ) : Prop :=
  ∃ q : Polynomial ℝ, affineBoydFormula n ell c q A

/-- The wall set supplied by the phase identity and the complete wall
arrangement. -/
def wallPredicate {n : ℕ} (ell : Polynomial ℝ) (v : Fin n → ℝ) : Prop :=
  (∃ u : ℝ,
    -2 < u ∧ u < 2 ∧ u ≠ 0 ∧
      Polynomial.eval u ell = 0 ∧
        Polynomial.eval u (correctionPolynomial v) = 0) ∨
    Polynomial.eval 0
      (ell - (2 : Polynomial ℝ) * correctionPolynomial v) = 0

def wallComplement {n : ℕ} (ell : Polynomial ℝ) : Set (Fin n → ℝ) :=
  {v | ¬ wallPredicate ell v}

/-- A maximal connected subset of the complement of the displayed walls. -/
def connectedComponent {n : ℕ}
    (U S : Set (Fin n → ℝ)) : Prop :=
  S ⊆ U ∧
    IsConnected S ∧
      ∀ T : Set (Fin n → ℝ),
        S ⊆ T → T ⊆ U → IsConnected T → T ⊆ S

/-- A Pisot Boyd chamber is defined as a connected wall component containing a
member with one positive exterior root.  The root-count conclusion is not
built into the chamber predicate. -/
def pisotChamber
    (n : ℕ) (ell : Polynomial ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  connectedComponent (wallComplement ell) S ∧
    ∃ v ∈ S, ∃ q A : Polynomial ℝ, ∃ θ : ℝ,
      affineBoydFormula n ell (correctionPolynomial v) q A ∧
        exteriorRoot A θ

/-- The ordered list is the complete list of nonzero real trace roots in the
interior interval. -/
def completeInteriorTraceRoots
    (n : ℕ) (ell : Polynomial ℝ) (u : Fin (n - 1) → ℝ) : Prop :=
  StrictMono u ∧
    (∀ i : Fin (n - 1),
      -2 < u i ∧ u i < 2 ∧ u i ≠ 0 ∧ Polynomial.eval (u i) ell = 0) ∧
      (∀ x : ℝ,
        -2 < x → x < 2 → x ≠ 0 → Polynomial.eval x ell = 0 →
          ∃ i : Fin (n - 1), u i = x)

/-- The last node is the exterior trace node. -/
def lastIndex {n : ℕ} (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩

def interiorIndex {n : ℕ} (hn : 0 < n) (i : Fin (n - 1)) : Fin n :=
  ⟨i.1, by omega⟩

def simplexNodes {n : ℕ}
    (u : Fin (n - 1) → ℝ) (x : ℝ) : Fin n → ℝ :=
  fun j => if h : j.1 < n - 1 then u ⟨j.1, h⟩ else x

/-- The closed same-chamber sublevel, expressed in the coefficient space of
corrections and using the actual affine Boyd member formula. -/
def closedRootSublevel
    (n : ℕ) (ell : Polynomial ℝ) (S : Set (Fin n → ℝ))
    (θstar : ℝ) : Set (Fin n → ℝ) :=
  {v | v ∈ closure S ∧
    ∃ q A : Polynomial ℝ, ∃ θ : ℝ,
      affineBoydFormula n ell (correctionPolynomial v) q A ∧
      exteriorRoot A θ ∧ θ ≤ θstar}

/-- The convex hull is written as the explicit finite convex-combination
carrier, so boundedness is not hidden in an arbitrary predicate. -/
def finiteConvexHull {n : ℕ}
    (vertices : Fin (n + 1) → Fin n → ℝ) : Set (Fin n → ℝ) :=
  {a | ∃ weights : Fin (n + 1) → ℝ,
    (∀ k : Fin (n + 1), 0 ≤ weights k) ∧
      Finset.sum Finset.univ weights = 1 ∧
      a = Finset.sum Finset.univ (fun k => weights k • vertices k)}

def boundedCoefficientSet {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ B : ℝ, ∀ a : Fin n → ℝ, a ∈ S →
    Finset.sum Finset.univ (fun i => |a i|) ≤ B

/-- Affine independence of `n+1` vertices in the `n` coefficient
coordinates, stated by the defining affine relation. -/
def affinelyIndependentVertices {n : ℕ}
    (vertices : Fin (n + 1) → Fin n → ℝ) : Prop :=
  ∀ weights : Fin (n + 1) → ℝ,
    Finset.sum Finset.univ weights = 0 →
      (∀ i : Fin n,
        Finset.sum Finset.univ (fun k => weights k * vertices k i) = 0) →
        ∀ k : Fin (n + 1), weights k = 0

/-- A genuine bounded `n`-simplex in the coefficient space. -/
def genuineBoundedSimplex {n : ℕ}
    (S : Set (Fin n → ℝ))
    (vertices : Fin (n + 1) → Fin n → ℝ) : Prop :=
  S = finiteConvexHull vertices ∧
    affinelyIndependentVertices vertices ∧
      boundedCoefficientSet S ∧ ∃ a : Fin n → ℝ, a ∈ S

/-- The simplex vertices: the base point and the `n` axis intercepts. -/
def simplexVertices {n : ℕ} (hn : 0 < n)
    (b : Polynomial ℝ) (L : Fin n → Polynomial ℝ)
    (d w : Fin n → ℝ) (H : ℝ) : Fin (n + 1) → Fin n → ℝ :=
  fun k => if h : k.1 = 0 then coefficientVector b else
    let j : Fin n := ⟨k.1 - 1, by omega⟩
    coefficientVector (b + ((H / (2 * w j)) * d j) • L j)

/-- Claim 25796: the positive Lagrange weights and the resulting genuine
bounded root-sublevel simplex. -/
def claim25796 : Prop :=
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
                    (Polynomial.eval 0 (traceToReal ell - (2 : Polynomial ℝ) * cstar))
                  let w : Fin n → ℝ := fun j =>
                    h * d j * Polynomial.eval 0 (L j)
                  let b := Polynomial.C (Polynomial.eval xstar cstar) * L last
                  let H := h *
                    (Polynomial.eval 0 (traceToReal ell) -
                      2 * Polynomial.eval 0 b)
                  (∀ j : Fin n, 0 < w j) ∧
                    h = Real.sign (Polynomial.eval 0 (traceToReal ell)) ∧
                      (∀ j : Fin n,
                        w j = |Polynomial.eval 0 (L j)|) ∧
                        0 < H ∧
                          genuineBoundedSimplex
                            (closedRootSublevel n (traceToReal ell) S θstar)
                            (simplexVertices hn b L d w H)

end MathlibPlus.Open.ResearchFormalization.BoydWeights25796
