import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.K0113.Claim8703

noncomputable section

/-- The finite probability/node/orthonormal-polynomial context of the
Christoffel kernels. -/
structure ChristoffelData where
  N : ℕ
  A : ℝ
  B : ℝ
  ν : MeasureTheory.Measure ℝ
  x : Fin N → ℝ
  ψ : Fin N → Polynomial ℝ
  interval : B > A
  probability : ν (Set.univ : Set ℝ) = 1
  support : MeasureTheory.Measure.support ν = Set.range x
  injective : Function.Injective x
  node_interval : ∀ i : Fin N, x i ∈ (Set.Icc A B : Set ℝ)
  degree : ∀ k : Fin N, (ψ k).degree = (k : WithBot ℕ)
  integrable : ∀ k : Fin N, Integrable (fun z : ℝ => (ψ k).eval z) ν
  orthonormal : ∀ k l : Fin N,
    ∫ z : ℝ, (ψ k).eval z * (ψ l).eval z ∂ν = if k = l then 1 else 0

/-- The ordinary Christoffel kernel `K_d(x,x)`. -/
def ordinaryChristoffelKernel_claim8703
    (D : ChristoffelData) (d : Fin D.N) (z : ℝ) : ℝ :=
  (Finset.univ.filter (fun k : Fin D.N => k.1 ≤ d.1)).sum
    (fun k => (D.ψ k).eval z ^ 2)

/-- The divided-difference Christoffel kernel at distinct support nodes. -/
def dividedChristoffelKernel_claim8703
    (D : ChristoffelData) (d : Fin D.N)
    (i j : Fin D.N) (hij : i ≠ j) : ℝ :=
  (Finset.univ.filter (fun k : Fin D.N => k.1 ≤ d.1)).sum
    (fun k =>
      (((D.ψ k).eval (D.x j) - (D.ψ k).eval (D.x i)) /
        (D.x i - D.x j)) ^ 2)

/-- The interval supremum `𝒦_d` of the ordinary kernel. -/
def christoffelKernelSupremum_claim8703
    (D : ChristoffelData) (d : Fin D.N) : ℝ :=
  sSup
    ((ordinaryChristoffelKernel_claim8703 D d) '' Set.Icc D.A D.B)

end

end MathlibPlus.Open.ResearchFormalization.K0113.Claim8703
