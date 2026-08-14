import Mathlib

noncomputable section
open Classical
attribute [local instance] Classical.decEq Classical.propDecidable

namespace MathlibPlus.Open.Analysis

private def endpointBlock (d : ℤ → ℝ) (k : ℕ) : Matrix (Fin 3) (Fin 2) ℝ :=
  fun i j => d ((k : ℤ) + (j.1 : ℤ) - (i.1 : ℤ))

private def endpointRow (m : Fin 3) (r : Fin 2) : Fin 3 :=
  if m.1 = 0 then
    if r.1 = 0 then 1 else 2
  else if m.1 = 1 then
    if r.1 = 0 then 0 else 2
  else if r.1 = 0 then 0 else 1

private def endpointMinor (d : ℤ → ℝ) (k : ℕ) (m : Fin 3) : ℝ :=
  Matrix.det (fun r c => endpointBlock d k (endpointRow m r) c)

private def endpointExplicitMinor (d : ℤ → ℝ) (k : ℕ) (m : Fin 3) : ℝ :=
  let q : ℤ → ℝ := fun t => d ((k : ℤ) + t)
  if m.1 = 0 then
    q (-1) * q (-1) - q 0 * q (-2)
  else if m.1 = 1 then
    q 0 * q (-1) - q 1 * q (-2)
  else
    q 0 * q 0 - q 1 * q (-1)

private def endpointSequence (c : ℕ → ℝ) (α b : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then c n.toNat else b * α ^ ((-n).toNat - 1)

def claim3051_rankTwoEndpointBlock : Prop :=
  ∀ (A : ℝ → ℝ) (a : ℕ → ℝ) (α : ℝ),
    0 < α →
    (∀ n, 0 < a n) →
    (∀ z : ℝ, HasSum (fun n => a n * z ^ n) (A z)) →
    let b := A α
    let c : ℕ → ℝ := fun n => ∑' j : ℕ, a (n + 1 + j) * α ^ j
    let d : ℤ → ℝ := endpointSequence c α b
    ∀ k : ℕ, 1 ≤ k →
      ∀ m : Fin 3, endpointExplicitMinor d k m = endpointMinor d k m

end MathlibPlus.Open.Analysis
