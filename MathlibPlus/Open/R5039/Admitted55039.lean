import Mathlib

namespace MathlibPlus.Open.R5039

open scoped BigOperators

/-- Coordinatewise nonnegativity for a finite-dimensional flow vector. -/
def nonnegativeVector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ x i

def flowFiber
    {σ : Type*} (n m : σ → ℕ)
    (A : ∀ s, (Fin (n s) → ℝ) →ₗ[ℝ] (Fin (m s) → ℝ))
    (b : ∀ s, Fin (m s) → ℝ) (s : σ) : Set (Fin (n s) → ℝ) :=
  {x | nonnegativeVector x ∧ A s x = b s}

def homogeneousFlowCone
    {σ : Type*} (n m : σ → ℕ)
    (A : ∀ s, (Fin (n s) → ℝ) →ₗ[ℝ] (Fin (m s) → ℝ)) (s : σ) :
    Set (Fin (n s) → ℝ) :=
  {r | nonnegativeVector r ∧ A s r = 0}

def projectedFlowFiber
    {σ : Type*}
    (n : σ → ℕ) (q : ℕ)
    (qmap : ∀ s, (Fin (n s) → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    (F : ∀ s, Set (Fin (n s) → ℝ)) (s : σ) : Set (Fin q → ℝ) :=
  qmap s '' F s

def finiteMinkowskiSum
    {σ Y : Type*} [Fintype σ]
    [AddCommGroup Y] [Module ℝ Y]
    (S : σ → Set Y) : Set Y :=
  {y | ∃ z : σ → Y, (∀ s, z s ∈ S s) ∧ (∑ s, z s) = y}

/-- Rationality of a finite-dimensional linear map in the displayed coordinate bases. -/
def hasRationalMatrix {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) : Prop :=
  ∃ a : Matrix (Fin m) (Fin n) ℚ,
    ∀ x i, A x i = ∑ j, (a i j : ℝ) * x j

def hasRationalVector {m : ℕ} (b : Fin m → ℝ) : Prop :=
  ∃ bq : Fin m → ℚ, ∀ i, b i = bq i

/-- Recession directions, including the requirement for every base point and every
nonnegative real multiple. -/
def recessionSet {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    (S : Set Y) : Set Y :=
  {r | ∀ x, x ∈ S → ∀ t : ℝ, 0 ≤ t → x + t • r ∈ S}

/-- Claim 55039: recession commutes with the nonnegative flow fibres, their linear
projections, and the finite Minkowski sum of the projected sectors. -/
def flowRecession_55039
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (n m : σ → ℕ) (q : ℕ)
    (A : ∀ s, (Fin (n s) → ℝ) →ₗ[ℝ] (Fin (m s) → ℝ))
    (b : ∀ s, Fin (m s) → ℝ)
    (qmap : ∀ s, (Fin (n s) → ℝ) →ₗ[ℝ] (Fin q → ℝ)) : Prop :=
  (∀ s, hasRationalMatrix (A s) ∧ hasRationalVector (b s) ∧
      hasRationalMatrix (qmap s)) →
  (∀ s, (flowFiber n m A b s).Nonempty) →
  (∀ s, recessionSet (flowFiber n m A b s) =
    homogeneousFlowCone n m A s) ∧
  (∀ s, recessionSet (projectedFlowFiber n q qmap (flowFiber n m A b) s) =
    qmap s '' homogeneousFlowCone n m A s) ∧
  recessionSet (finiteMinkowskiSum (projectedFlowFiber n q qmap (flowFiber n m A b))) =
    finiteMinkowskiSum (fun s => qmap s '' homogeneousFlowCone n m A s)

end MathlibPlus.Open.R5039
