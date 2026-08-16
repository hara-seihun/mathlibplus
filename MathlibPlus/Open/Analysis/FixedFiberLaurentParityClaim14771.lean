import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.Open.Analysis

/-- An invertible continuous linear map on the fixed fiber. -/
def fixedFiberInvertibleAtZero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (A : V →L[ℂ] V) : Prop :=
  ∃ B : V →L[ℂ] V,
    B.comp A = ContinuousLinearMap.id ℂ V ∧
      A.comp B = ContinuousLinearMap.id ℂ V

/-- Claim 14771: the leading Laurent coefficient of a reflection-compatible
fixed-fiber family lies in the parity eigenspace of the fiber involution. -/
def fixedFiberLaurentParityClaim14771 : Prop :=
  ∀ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : ℂ → V) (N : ℂ → (V →L[ℂ] V)) (m : ℤ) (v : V),
    (∀ ε : ℂ, f (-ε) = N ε (f ε)) ∧
    (∀ ε : ℂ, (N (-ε)).comp (N ε) = ContinuousLinearMap.id ℂ V) ∧
    AnalyticAt ℂ N 0 ∧
    fixedFiberInvertibleAtZero (N 0) ∧
    v ≠ 0 ∧
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun ε => f ε - (ε ^ m) • v)
      (fun ε => ε ^ (m + 1)) →
      N 0 v = ((-1 : ℂ) ^ m) • v

end MathlibPlus.Open.Analysis
