import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis.BooleanChamberBatch

abbrev BooleanAtom (q : ℕ) := Fin q → Bool
abbrev BooleanPolicy (q : ℕ) := BooleanAtom q → Bool

structure LossTable (q : ℕ) where
  loss : BooleanPolicy q → BooleanAtom q → ℝ

def CommonActiveChamber {q k : ℕ} (L : LossTable q)
    (selected : Fin k → BooleanPolicy q) (tau : BooleanPolicy q) :
    Set (BooleanAtom q → ℝ) :=
  {u | (∀ μ : BooleanAtom q, 0 ≤ u μ) ∧
    (∑ μ : BooleanAtom q, u μ = 1) ∧
    (∀ i : Fin k, ∀ μ : BooleanAtom q,
      L.loss (selected i) μ ≤ L.loss tau μ)}

def ActivityGapsNonnegative {q k : ℕ} (L : LossTable q)
    (selected : Fin k → BooleanPolicy q) (tau : BooleanPolicy q) : Prop :=
  ∀ u ∈ CommonActiveChamber L selected tau,
    ∀ i : Fin k, ∀ μ : BooleanAtom q,
      0 ≤ u μ * (L.loss tau μ - L.loss (selected i) μ)

def BernsteinIndex :=
  {e : Fin 4 → Fin 4 // ∑ i : Fin 4, (e i).val = 3}

noncomputable instance : Fintype BernsteinIndex := Subtype.fintype _

def bernsteinBasis (e : BernsteinIndex) (u : Fin 4 → ℝ) : ℝ :=
  (Nat.factorial 3 : ℝ) /
      (∏ i : Fin 4, (Nat.factorial (e.1 i).val : ℝ)) *
    ∏ i : Fin 4, u i ^ (e.1 i).val

def bernsteinPolynomial (b : BernsteinIndex → ℝ) (u : Fin 4 → ℝ) : ℝ :=
  ∑ e : BernsteinIndex, b e * bernsteinBasis e u

def bernsteinSimplex (u : Fin 4 → ℝ) : Prop :=
  (∀ i : Fin 4, 0 ≤ u i) ∧ ∑ i : Fin 4, u i = 1

def bernsteinGapPolynomial {s : ℕ} (A : BernsteinIndex → Fin s → ℝ)
    (i : Fin s) (u : Fin 4 → ℝ) : ℝ :=
  ∑ e : BernsteinIndex, A e i * bernsteinBasis e u

def bernsteinPrimalFeasible {s : ℕ} (b : BernsteinIndex → ℝ)
    (A : BernsteinIndex → Fin s → ℝ) : Prop :=
  ∃ α : Fin s → ℝ,
    (∀ i : Fin s, 0 ≤ α i) ∧
    (∀ e : BernsteinIndex,
      b e + ∑ i : Fin s, A e i * α i ≤ 0)

def bernsteinDualWitness {s : ℕ} (b : BernsteinIndex → ℝ)
    (A : BernsteinIndex → Fin s → ℝ) (y : BernsteinIndex → ℝ) : Prop :=
  (∀ e : BernsteinIndex, 0 ≤ y e) ∧
    (∀ i : Fin s, 0 ≤ ∑ e : BernsteinIndex, A e i * y e) ∧
    0 < ∑ e : BernsteinIndex, b e * y e

def BernsteinCoefficientFarkasAndNormalization : Prop :=
  ∀ (s : ℕ) (b : BernsteinIndex → ℝ)
    (A : BernsteinIndex → Fin s → ℝ),
    (bernsteinPrimalFeasible b A ↔
      ¬ ∃ y : BernsteinIndex → ℝ, bernsteinDualWitness b A y) ∧
    (∀ y : BernsteinIndex → ℝ, bernsteinDualWitness b A y →
      ∃ y' : BernsteinIndex → ℝ,
        bernsteinDualWitness b A y' ∧
          (∑ e : BernsteinIndex, y' e = 1) ∧
          (∀ e : BernsteinIndex,
            y' e = y e / ∑ f : BernsteinIndex, y f))

def CoefficientwiseCubicActivityMajorantSound : Prop :=
  ∀ (s : ℕ) (b : BernsteinIndex → ℝ)
    (A : BernsteinIndex → Fin s → ℝ)
    (α : Fin s → ℝ) (u : Fin 4 → ℝ),
    (∀ i : Fin s, 0 ≤ α i) →
    bernsteinSimplex u →
    (∀ i : Fin s, 0 ≤ bernsteinGapPolynomial A i u) →
    (∀ e : BernsteinIndex,
      b e + ∑ i : Fin s, A e i * α i ≤ 0) →
    bernsteinPolynomial b u ≤ 0

abbrev TripleTensor (n : ℕ) := (Fin 3 → Fin n) → ℝ

def tripleMultiset {n : ℕ} (x : Fin 3 → Fin n) : Multiset (Fin n) :=
  ({x 0, x 1, x 2} : Multiset (Fin n))

def TensorNonnegativeAndNormalized {n : ℕ} (T : TripleTensor n) : Prop :=
  (∀ x : Fin 3 → Fin n, 0 ≤ T x) ∧
    ∑ x : Fin 3 → Fin n, T x = 1

def TensorExchangeable {n : ℕ} (T : TripleTensor n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → Fin n),
    T x = T (x ∘ σ)

def tripleFiberCard {n : ℕ} (s : Multiset (Fin n)) : ℕ :=
  Fintype.card {x : Fin 3 → Fin n // tripleMultiset x = s}

def tripleMultisetMass {n : ℕ} (T : TripleTensor n) (s : Multiset (Fin n)) : ℝ :=
  ∑ x : Fin 3 → Fin n,
    if tripleMultiset x = s then T x else 0

def IsExchangeableMultisetLaw {n : ℕ} (T : TripleTensor n) : Prop :=
  TensorNonnegativeAndNormalized T ∧
    TensorExchangeable T ∧
    (∀ x : Fin 3 → Fin n, 0 < tripleFiberCard (tripleMultiset x)) ∧
    (∀ x : Fin 3 → Fin n,
      T x = tripleMultisetMass T (tripleMultiset x) /
        (tripleFiberCard (tripleMultiset x) : ℝ))

def NormalizedSymmetricTensorIsMultisetLaw : Prop :=
  ∀ (n : ℕ) (T : TripleTensor n),
    TensorNonnegativeAndNormalized T → TensorExchangeable T →
      IsExchangeableMultisetLaw T

def twoPointExchangeableTensor : TripleTensor 2 :=
  fun x =>
    if ((x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1) ∨
        (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 0) ∨
        (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 0)) then
      (1 : ℝ) / 3
    else 0

def simplexPoint (n : ℕ) :=
  {p : Fin n → ℝ // (∀ i : Fin n, 0 ≤ p i) ∧ ∑ i : Fin n, p i = 1}

def IsIIDMixture {n : ℕ} (T : TripleTensor n) : Prop :=
  ∃ μ : Measure (Fin n → ℝ),
    IsProbabilityMeasure μ ∧
    (∀ᵐ p ∂μ, (∀ i : Fin n, 0 ≤ p i) ∧ ∑ i : Fin n, p i = 1) ∧
    (∀ x : Fin 3 → Fin n,
      T x = ∫ p, ∏ j : Fin 3, p (x j) ∂μ)

def TwoPointExchangeableIsNotIID : Prop :=
  IsExchangeableMultisetLaw twoPointExchangeableTensor ∧
    twoPointExchangeableTensor (fun _ : Fin 3 => 0) = 0 ∧
    ¬ IsIIDMixture twoPointExchangeableTensor

def ExchangeableTensorMixtureSeparation : Prop :=
  NormalizedSymmetricTensorIsMultisetLaw ∧ TwoPointExchangeableIsNotIID

end MathlibPlus.Open.Analysis.BooleanChamberBatch
