import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatch

open scoped BigOperators
open Filter MeasureTheory Set

noncomputable section

/-- The cardinal polynomial of a node in a finite interpolation row. -/
def cardinalPolynomial {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) : Polynomial ℝ :=
  Polynomial.C
      (∏ j ∈ Finset.univ.erase i, (nodes i - nodes j)⁻¹) *
    (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (nodes j)))

/-- The Lebesgue function associated with a finite row of nodes. -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |(cardinalPolynomial nodes i).eval x|

def prefixNodes (t : ℕ → ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => t i.1

def globalLebesgueMaximum {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  sSup (lebesgueFunction nodes '' Set.Icc (-1 : ℝ) 1)

def infinitelyOften (p : ℕ → Prop) : Prop :=
  Set.Infinite {n | p n}

def sharpLimsupAtLeast (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, a - ε < f n

/-- The first-kind Chebyshev functions, with the standard recurrence. -/
def chebyshev : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | k + 2, x => 2 * x * chebyshev (k + 1) x - chebyshev k x

/-- Essential-supremum form of the L-infinity norm on a measurable region. -/
def linftyNormOn (f : ℝ → ℝ) (I : Set ℝ) : ℝ :=
  sInf {B : ℝ | ∀ᵐ x ∂(volume.restrict I), |f x| ≤ B}

/-- Claim 16722: the original universal fixed-point sharp-divergence assertion. -/
def nestedNodeFixedPointSharpDivergence : Prop :=
  ∀ t : ℕ → ℝ,
    (∀ m, t m ∈ Set.Icc (-1 : ℝ) 1) →
    Function.Injective t →
    ∃ x ∈ Set.Ioo (-1 : ℝ) 1, ∃ C : ℝ,
      infinitelyOften (fun n =>
        0 < n ∧
          (2 / Real.pi) * Real.log (n : ℝ) - C <
            lebesgueFunction (prefixNodes t n) x)

/-- The explicit alternating dyadic node sequence from Claim 16723. -/
def alternatingDyadicNodes (r : ℕ) : ℝ :=
  if r % 2 = 0 then
    (2 : ℝ)⁻¹ ^ (r / 2 + 1)
  else
    -((2 : ℝ)⁻¹ ^ (r / 2 + 1))

/-- Claim 16723: the bounded-point nested counterexample. -/
def alternatingDyadicCounterexample : Prop :=
  Function.Injective alternatingDyadicNodes ∧
    (∀ r, alternatingDyadicNodes r ≠ 0) ∧
    ∃ B : ℝ, ∀ n,
      lebesgueFunction (prefixNodes alternatingDyadicNodes n) 0 ≤ B

/-- Claim 16725: the finite-row global maximum lower bound. -/
def finiteNodeGlobalMaximumLowerBound : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 0 < n →
    ∀ nodes : Fin n → ℝ,
      Function.Injective nodes →
      (∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1) →
      globalLebesgueMaximum nodes >
        (2 / Real.pi) * Real.log (n : ℝ) - C

/-- Claim 16726: the sharp limsup set is dense in the open interval. -/
def denseSetOfSharpLimsup : Prop :=
  ∀ t : ℕ → ℝ,
    (∀ m, t m ∈ Set.Icc (-1 : ℝ) 1) →
    Function.Injective t →
    ∀ a b : ℝ, -1 < a → a < b → b < 1 →
      ∃ x ∈ Set.Ioo a b,
        sharpLimsupAtLeast
          (fun n =>
            lebesgueFunction (prefixNodes t n) x /
              Real.log (n : ℝ))
          (2 / Real.pi)

/-- Claim 16727: a fixed interior interval has a row-dependent lower bound. -/
def intervalLocalFiniteRowLowerBound : Prop :=
  ∀ a b : ℝ, -1 < a → a < b → b < 1 →
    ∃ N : ℕ, ∃ C : ℝ, ∀ n : ℕ, N ≤ n → 0 < n →
      ∀ nodes : Fin n → ℝ,
        Function.Injective nodes →
        (∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1) →
        ∃ x ∈ Set.Ioo a b,
          lebesgueFunction nodes x ≥
            (2 / Real.pi) * Real.log (n : ℝ) - C

/-- Claim 16730: the exact measurable-set Remez transfer for the Lebesgue function. -/
def measurableSetRemezTransfer : Prop :=
  ∀ (n : ℕ) (a b : ℝ) (nodes : Fin (n + 1) → ℝ)
    (E : Set ℝ) (B : ℝ),
    a < b →
    Function.Injective nodes →
    MeasurableSet E →
    E ⊆ Set.Icc a b →
    let I := Set.Icc a b
    let θ := (volume E).toReal / (volume I).toReal
    0 < θ →
    (∀ x, x ∈ E → lebesgueFunction nodes x ≤ B) →
    linftyNormOn (lebesgueFunction nodes) I ≤
      chebyshev n (2 / θ - 1) * B

end
end MathlibPlus.Open.Analysis.FormalizationBatch
