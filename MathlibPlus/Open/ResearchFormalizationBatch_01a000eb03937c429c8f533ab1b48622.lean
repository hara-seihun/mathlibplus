import Mathlib

open scoped Topology

namespace MathlibPlus.Open.ResearchFormalizationBatch01

noncomputable def offRealSymmetric (Δ : Multiset ℂ) : Prop :=
  (∀ z : ℂ, z ∈ Δ → z.im ≠ 0) ∧
    Δ.map (fun z : ℂ => -z) = Δ ∧
    Δ.map (fun z : ℂ => star z) = Δ

/-- Every finite divisor off the real axis with the stated symmetries has the
prescribed positive even polynomial factorization. -/
def claim9931 : Prop :=
  ∀ Δ : Multiset ℂ, offRealSymmetric Δ →
    ∃ Q : Polynomial ℝ,
      (∀ x : ℝ, 0 < Q.eval (x ^ 2)) ∧
      (((Q.map Complex.ofRealHom).comp (Polynomial.X ^ 2)).roots = Δ)

noncomputable def cornerA (p : ℕ) : ℝ := (Real.sqrt (p : ℝ))⁻¹

noncomputable def cornerX {d : ℕ} (x : Fin d → ℂ) : ℂ :=
  ∏ j, x j

noncomputable def cornerQ0 {d : ℕ} (p : Fin d → ℕ) (x : Fin d → ℂ) : ℂ :=
  ∏ j, (1 - (cornerA (p j) : ℂ) * x j)

noncomputable def cornerQM {d : ℕ} (p : Fin d → ℕ) (M : ℕ)
    (x : Fin d → ℂ) : ℂ :=
  cornerQ0 p x + cornerX x ^ (2 * M - 1) *
    ∏ j, (x j - (cornerA (p j) : ℂ))

noncomputable def cornerPM {d : ℕ} (M : ℕ) (c : ℝ)
    (x : Fin d → ℂ) : ℂ :=
  1 + (c : ℂ) * cornerX x ^ M + cornerX x ^ (2 * M)

noncomputable def cornerXPoly {d : ℕ} : MvPolynomial (Fin d) ℂ :=
  ∏ j, MvPolynomial.X j

noncomputable def cornerPMPoly {d : ℕ} (M : ℕ) (c : ℝ) :
    MvPolynomial (Fin d) ℂ :=
  MvPolynomial.C 1 + MvPolynomial.C (c : ℂ) * cornerXPoly ^ M +
    cornerXPoly ^ (2 * M)

noncomputable def cornerQ0Poly {d : ℕ} (p : Fin d → ℕ) :
    MvPolynomial (Fin d) ℂ :=
  ∏ j, (1 - MvPolynomial.C (cornerA (p j) : ℂ) * MvPolynomial.X j)

noncomputable def cornerQMPoly {d : ℕ} (p : Fin d → ℕ) (M : ℕ) :
    MvPolynomial (Fin d) ℂ :=
  cornerQ0Poly p + cornerXPoly ^ (2 * M - 1) *
    ∏ j, (MvPolynomial.X j - MvPolynomial.C (cornerA (p j) : ℂ))

noncomputable def reciprocalInVariables {d : ℕ}
    (f : (Fin d → ℂ) → ℂ) (degree : ℕ) : Prop :=
  ∀ x : Fin d → ℂ, (∀ j, x j ≠ 0) →
    f (fun j => (x j)⁻¹) = (cornerX x)⁻¹ ^ degree * f x

/-- The full-corner reciprocal polynomial identities, with all carriers made
explicit as functions of the finitely many variables. -/
def claim10031 : Prop :=
  ∀ (d M : ℕ) (p : Fin d → ℕ) (c : ℝ),
    2 ≤ d → 1 ≤ M →
    (∀ j, Nat.Prime (p j)) →
    Function.Injective p →
    (∀ j : Fin d, (cornerPMPoly (d := d) M c).degreeOf j = 2 * M) ∧
    (∀ j : Fin d, (cornerQMPoly (d := d) p M).degreeOf j = 2 * M) ∧
    reciprocalInVariables (d := d) (cornerPM (d := d) M c) (2 * M) ∧
      reciprocalInVariables (d := d) (cornerQM (d := d) p M) (2 * M) ∧
      (∀ x : Fin d → ℂ, (∀ j, x j ≠ 0) →
        cornerQM p M x =
          cornerQ0 p x + cornerX x ^ (2 * M) *
            (∏ j, (1 - (cornerA (p j) : ℂ) * (x j)⁻¹))) ∧
      (∀ x : Fin d → ℂ,
        cornerX x ^ (2 * M) *
            (∏ j, (1 - (cornerA (p j) : ℂ) * (x j)⁻¹)) =
          cornerX x ^ (2 * M - 1) *
            ∏ j, (x j - (cornerA (p j) : ℂ)))

noncomputable def blaschkeFactor (a : ℝ) (z : ℂ) : ℂ :=
  (z - (a : ℂ)) / (1 - (a : ℂ) * z)

noncomputable def cornerSourcePoint {d : ℕ} (p : Fin d → ℕ)
    (s : ℂ) : Fin d → ℂ :=
  fun j => Complex.exp
    (((1 / 2 : ℂ) - s) * (Real.log (p j : ℝ) : ℂ))

/-- Blaschke stability and its zero-free/right-half-plane consequence for the
explicit full-corner denominator. -/
def claim10034 : Prop :=
  (∀ (a : ℝ) (z : ℂ), 0 < a → a < 1 → ‖z‖ < 1 →
    ‖blaschkeFactor a z‖ < 1) ∧
    ∀ (d M : ℕ) (p : Fin d → ℕ),
      2 ≤ d → 1 ≤ M →
      (∀ j, Nat.Prime (p j)) →
      Function.Injective p →
      (∀ x : Fin d → ℂ,
        (∀ j, 1 - (cornerA (p j) : ℂ) * x j ≠ 0) →
        cornerQM p M x =
          cornerQ0 p x *
            (1 + cornerX x ^ (2 * M - 1) *
              ∏ j, blaschkeFactor (cornerA (p j)) (x j))) ∧
      (∀ x : Fin d → ℂ, (∀ j, ‖x j‖ < 1) →
        cornerQM p M x ≠ 0) ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        cornerQM p M (cornerSourcePoint p s) ≠ 0) ∧
      (∀ s : ℂ,
        cornerQM p M (cornerSourcePoint p s) = 0 → s.re = 1 / 2)

noncomputable def cornerCommonZeroParameters {d : ℕ}
    (p : Fin d → ℕ) (M : ℕ) : Set ℝ :=
  {c | ∃ s : ℂ,
    cornerQM p M (cornerSourcePoint p s) = 0 ∧
      cornerPM M c (cornerSourcePoint p s) = 0}

noncomputable def cornerNumeratorAlong {d : ℕ}
    (p : Fin d → ℕ) (M : ℕ) (c : ℝ) (s : ℂ) : ℂ :=
  cornerPM M c (cornerSourcePoint p s)

noncomputable def cornerDenominatorAlong {d : ℕ}
    (p : Fin d → ℕ) (M : ℕ) (s : ℂ) : ℂ :=
  cornerQM p M (cornerSourcePoint p s)

noncomputable def cornerQuotient {d : ℕ}
    (p : Fin d → ℕ) (M : ℕ) (c : ℝ) (s : ℂ) : ℂ :=
  cornerNumeratorAlong p M c s / cornerDenominatorAlong p M s

noncomputable def cornerZeroCount {d : ℕ}
    (p : Fin d → ℕ) (M : ℕ) (c : ℝ) (T : ℝ) : ℕ :=
  Set.ncard {s : ℂ |
    cornerNumeratorAlong p M c s = 0 ∧
      cornerDenominatorAlong p M s ≠ 0 ∧ |s.im| ≤ T}

noncomputable def cornerPoleCount {d : ℕ}
    (p : Fin d → ℕ) (M : ℕ) (c : ℝ) (T : ℝ) : ℕ :=
  Set.ncard {s : ℂ |
    cornerDenominatorAlong p M s = 0 ∧
      cornerNumeratorAlong p M c s ≠ 0 ∧ |s.im| ≤ T}

/-- The critical-line branch, including the reduced-divisor simplicity and
counting assertions. -/
def claim10035 : Prop :=
  ∀ (d M : ℕ) (p : Fin d → ℕ),
    2 ≤ d → 1 ≤ M →
    (∀ j, Nat.Prime (p j)) →
    Function.Injective p →
    ∃ E : Set ℝ, E.Countable ∧
      ∃ C T₀ : ℝ, 0 < C ∧ 0 ≤ T₀ ∧
        ∀ c : ℝ, c ∈ Set.Ioo (-2) 2 → c ∉ E →
          DifferentiableOn ℂ (cornerQuotient p M c)
            {s : ℂ | 1 / 2 < s.re} ∧
          (∀ s : ℂ, 1 / 2 < s.re →
            cornerQuotient p M c s ≠ 0) ∧
          (∀ s : ℂ,
            cornerNumeratorAlong p M c s = 0 ∧
              cornerDenominatorAlong p M s ≠ 0 →
              deriv (cornerNumeratorAlong p M c) s ≠ 0 ∧ s.re = 1 / 2) ∧
          (∀ s : ℂ,
            cornerDenominatorAlong p M s = 0 ∧
              cornerNumeratorAlong p M c s ≠ 0 →
              deriv (cornerDenominatorAlong p M) s ≠ 0 ∧ s.re = 1 / 2) ∧
          (∀ T : ℝ, T₀ ≤ T →
            |(cornerZeroCount p M c T : ℝ) -
                (2 * (M : ℝ) * (∑ j, Real.log (p j : ℝ)) / Real.pi) * T| ≤ C) ∧
          (∀ T : ℝ, T₀ ≤ T →
            |(cornerPoleCount p M c T : ℝ) -
                (2 * (M : ℝ) * (∑ j, Real.log (p j : ℝ)) / Real.pi) * T| ≤ C)

/-- Countability of critical-line denominator zeros and of the parameter set
where a numerator and denominator zero can cancel. -/
def claim10037 : Prop :=
  ∀ (d M : ℕ) (p : Fin d → ℕ),
    2 ≤ d → 1 ≤ M →
    (∀ j, Nat.Prime (p j)) →
    Function.Injective p →
    Set.Countable
        {s : ℂ | s.re = 1 / 2 ∧
          cornerQM p M (cornerSourcePoint p s) = 0} ∧
      (∀ s : ℂ, cornerQM p M (cornerSourcePoint p s) = 0 →
        ∀ c₁ c₂ : ℝ, c₁ ∈ Set.Icc (-2) 2 → c₂ ∈ Set.Icc (-2) 2 →
          cornerPM M c₁ (cornerSourcePoint p s) = 0 →
          cornerPM M c₂ (cornerSourcePoint p s) = 0 → c₁ = c₂) ∧
      Set.Countable (cornerCommonZeroParameters p M) ∧
      (∀ c : ℝ, c ∈ Set.Ioo (-2) 2 →
        c ∉ cornerCommonZeroParameters p M →
        ∀ s : ℂ,
          cornerQM p M (cornerSourcePoint p s) = 0 →
            cornerPM M c (cornerSourcePoint p s) ≠ 0)

noncomputable def vonMangoldtReal (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ p : ℕ, Nat.Prime p ∧ ∃ k : ℕ, 0 < k ∧ n = p ^ k then
    let p : ℕ := Classical.choose h
    Real.log (p : ℝ)
  else 0

noncomputable def weightedVonMangoldtSum (T : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.floor (Real.exp T)))
    (fun m => vonMangoldtReal m / (m : ℝ))

noncomputable def eulerGamma : ℝ :=
  Filter.limUnder Filter.atTop
    (fun n : ℕ =>
      (Finset.sum (Finset.range n) (fun k => (1 : ℝ) / (k + 1))) -
        Real.log (n : ℝ))

/-- The stated weighted prime discrepancy estimate, with big-O expanded into
its usual eventual inequality. -/
def claim10108 : Prop :=
  ∃ c C T₀ : ℝ,
    0 < c ∧ 0 < C ∧ 0 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        |weightedVonMangoldtSum T - T + eulerGamma| ≤
          C * (1 + Real.sqrt T) * Real.exp (-c * Real.sqrt T)

noncomputable def signedPoissonSequence (n : ℕ) : ℝ :=
  (((2 : ℂ) * Complex.I) ^ n + ((-2 : ℂ) * Complex.I) ^ n).re

/-- The explicit signed Poisson counterexample and its unbounded positive
subsequence. -/
def claim10114 : Prop :=
  (∀ k : ℕ, signedPoissonSequence (4 * k) = (2 : ℝ) ^ (4 * k + 1)) ∧
    (∀ k : ℕ, signedPoissonSequence (4 * k + 2) = -(2 : ℝ) ^ (4 * k + 3)) ∧
    (∀ k : ℕ, signedPoissonSequence (2 * k + 1) = 0) ∧
    (∀ x : ℝ, 0 ≤ x →
      HasSum
        (fun n : ℕ => Real.exp (-x) * x ^ n / (n.factorial : ℝ) *
          signedPoissonSequence n)
        (2 * Real.exp (-x) * Real.cos (2 * x))) ∧
    (∀ x : ℝ, 0 ≤ x →
      |2 * Real.exp (-x) * Real.cos (2 * x)| ≤ 2 * Real.exp (-x)) ∧
    (∀ B : ℝ, ∃ k : ℕ, B < signedPoissonSequence (4 * k)) ∧
    Filter.Tendsto (fun x : ℝ => 2 * Real.exp (-x) * Real.cos (2 * x))
      Filter.atTop (𝓝 0)

end MathlibPlus.Open.ResearchFormalizationBatch01
