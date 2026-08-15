import Mathlib

namespace MathlibPlus.Open.Formalization.TopologicalUnimodal

noncomputable section

open scoped BigOperators

/-- The point `0` in the interval `[-eta,0]`, when the interval is nonempty. -/
def intervalZero (eta : ℝ) (h : 0 ≤ eta) : Set.Icc (-eta) 0 :=
  ⟨0, by constructor <;> linarith⟩

/-- Claim 56552, stated on the interval appearing in the packet. -/
def claim56552 : Prop :=
  ∀ (eta : ℝ) (A : Type*) [TopologicalSpace A] [T2Space A]
    [LocallyCompactSpace A],
    ∀ (h_eta : 0 ≤ eta),
      ∀ (m : A × Set.Icc (-eta) 0 → ℝ) (P : ℝ → Prop),
        Continuous m →
          (∀ t : Set.Icc (-eta) 0,
              (∀ a : A, 0 < m (a, t)) → P (t : ℝ)) →
          (∀ a : A, 0 < m (a, intervalZero eta h_eta)) →
          (∀ t : ℝ, t < 0 → ¬ P t) →
          ∀ K : Set A, IsCompact K →
            ∃ epsilon : ℝ, epsilon > 0 ∧
              ∀ a : A, a ∈ K →
                ∀ t : Set.Icc (-eta) 0,
                  -epsilon < (t : ℝ) → (t : ℝ) ≤ 0 →
                    0 < m (a, t)

/-- Finitely supported sequences on the integer line. -/
def finiteSequence (f : ℤ → ℝ) : Prop :=
  Set.Finite (Function.support f)

def nonnegativeSequence (f : ℤ → ℝ) : Prop :=
  ∀ i : ℤ, 0 ≤ f i

def logConcaveNoInternalZeros (f : ℤ → ℝ) : Prop :=
  (∀ i : ℤ, f i ^ 2 ≥ f (i - 1) * f (i + 1)) ∧
    (∀ i j k : ℤ, i < j → j < k → f i ≠ 0 → f k ≠ 0 → f j ≠ 0)

def unimodal (f : ℤ → ℝ) : Prop :=
  ∃ mode : ℤ,
    (∀ i j : ℤ, i ≤ j → j ≤ mode → f i ≤ f j) ∧
    (∀ i j : ℤ, mode ≤ i → i ≤ j → f j ≤ f i)

def discreteConvolution (a b : ℤ → ℝ) : ℤ → ℝ :=
  fun k => ∑' j : ℤ, a (k - j) * b j

/-- Claim 56915: log-concave factors with no internal zeros preserve unimodality. -/
def claim56915 : Prop :=
  ∀ (a b : ℤ → ℝ),
    finiteSequence a → finiteSequence b →
      nonnegativeSequence a → nonnegativeSequence b →
      logConcaveNoInternalZeros a → unimodal b →
      unimodal (discreteConvolution a b)

end

end MathlibPlus.Open.Formalization.TopologicalUnimodal
