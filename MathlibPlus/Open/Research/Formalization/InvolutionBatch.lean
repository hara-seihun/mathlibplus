import Mathlib

namespace MathlibPlus.Open.Research.InvolutionBatch

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

def signedInvolutionSum {C : Type*} [Fintype C] (s W : C → ℝ) : ℝ :=
  ∑ c : C, s c * W c

def fixedLocusWeight {C : Type*} [Fintype C] (iota : C → C) (W : C → ℝ) : ℝ :=
  Finset.sum (Finset.univ.filter (fun c : C => iota c = c)) W

def involutionHypotheses {C : Type*} [Fintype C]
    (iota : C → C) (s W : C → ℝ) : Prop :=
  Function.Involutive iota ∧
    (∀ c : C, W (iota c) = W c) ∧
    (∀ c : C, iota c ≠ c → s (iota c) = -s c) ∧
    (∀ c : C, iota c = c → s c = 1)

def claim_59485 : Prop :=
  ∀ {C : Type*} [Fintype C]
    (iota : C → C) (s : C → ℝ) (W : C → ℝ),
    (∀ c : C, 0 < W c) →
    involutionHypotheses iota s W →
      signedInvolutionSum s W = fixedLocusWeight iota W ∧
      ((∃ c : C, iota c = c) → 0 < signedInvolutionSum s W) ∧
      (signedInvolutionSum s W ≤ 0 → ¬ ∃ c : C, iota c = c)

end
end MathlibPlus.Open.Research.InvolutionBatch
