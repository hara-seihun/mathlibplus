import Mathlib

namespace MathlibPlus.Open.Combinatorics.PathDualLipschitzCalibration

open scoped BigOperators

noncomputable section

/-- Coefficients of a finite event chain on the formal ordered vertices
`v₀, ..., v_N`. -/
def PathChain (N : ℕ) := Fin (N + 1) → ℝ

/-- The zero-total-mass condition on a path event chain. -/
def zeroMassChain {N : ℕ} (e : PathChain N) : Prop :=
  ∑ j : Fin (N + 1), e j = 0

/-- Prefix charge on the edge from vertex `k` to vertex `k+1`. -/
def prefixCharge {N : ℕ} (e : PathChain N) (k : Fin N) : ℝ :=
  ∑ j ∈ Finset.Iic (Fin.castSucc k), e j

/-- The canonical transport filling has coefficient `-S_k` on the edge
from `v_k` to `v_{k+1}`. -/
def canonicalFilling {N : ℕ} (e : PathChain N) : Fin N → ℝ :=
  fun k => -prefixCharge e k

/-- The coefficient ℓ¹ norm of a path filling. -/
def fillingL1Norm {N : ℕ} (h : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, |h k|

/-- Functions on the formal vertices whose adjacent increments have modulus at
most one. -/
def pathLipschitz {N : ℕ} (f : Fin (N + 1) → ℝ) : Prop :=
  ∀ k : Fin N,
    |f (Fin.succ k) - f (Fin.castSucc k)| ≤ 1

/-- The exact finite dual value over the path-Lipschitz class. -/
noncomputable def dualLipschitzValue {N : ℕ} (e : PathChain N) : ℝ :=
  sSup {x : ℝ | ∃ f : Fin (N + 1) → ℝ,
    pathLipschitz f ∧ x = |∑ j : Fin (N + 1), e j * f j|}

/-- Claim 15222: the canonical filling is calibrated by the dual
1-Lipschitz path functions. -/
def claim15222 : Prop :=
  ∀ {N : ℕ} (e : PathChain N),
    zeroMassChain e →
      fillingL1Norm (canonicalFilling e) = dualLipschitzValue e

end
end MathlibPlus.Open.Combinatorics.PathDualLipschitzCalibration
