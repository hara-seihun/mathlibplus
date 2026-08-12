import Mathlib

namespace MathlibPlus.GroupTheory.Claim28503

/-- The mixed multiplicative/additive product law for `K × H`. -/
def directProductMul {K H : Type*} [Group K] [AddGroup H]
    (p q : K × H) : K × H :=
  (p.1 * q.1, p.2 + q.2)

/-- Inverse for the mixed direct-product law. -/
def directProductInv {K H : Type*} [Group K] [AddGroup H]
    (p : K × H) : K × H :=
  (p.1⁻¹, -p.2)

/-- The direct-product map that leaves the finite-group coordinate fixed. -/
def directProductMap {K H : Type*} [Group K] [AddGroup H]
    (σ : Equiv.Perm H) : K × H → K × H :=
  fun p => (p.1, σ p.2)

/-- The inverse of the direct-product map. -/
def directProductMapInv {K H : Type*} [Group K] [AddGroup H]
    (σ : Equiv.Perm H) : K × H → K × H :=
  fun p => (p.1, σ.symm p.2)

/-- The normalized relative derivative formula from claim 28503, defined by
`f⁻¹ (f(p * (u,t)) * f(u,t)⁻¹)` for the displayed direct-product map. -/
def directProductRelativeDerivative {K H : Type*} [Group K] [AddGroup H]
    (σ : Equiv.Perm H) (u : K) (t : H) : K × H → K × H :=
  fun p =>
    directProductMapInv σ
      (directProductMul
        (directProductMap σ (directProductMul p (u, t)))
        (directProductInv (directProductMap σ (u, t))))

/-- Exact application of the direct-product relative-derivative formula. -/
theorem directProductRelativeDerivative_apply_claim28503
    {K H : Type*} [Fintype K] [Group K] [Fintype H] [AddCommGroup H]
    (σ : Equiv.Perm H) (u : K) (t : H) (k : K) (h : H) :
    directProductRelativeDerivative σ u t (k, h) =
      (k, σ.symm (σ (h + t) - σ t)) := by
  simp [directProductRelativeDerivative, directProductMapInv, directProductMul,
    directProductInv, directProductMap, sub_eq_add_neg]

end MathlibPlus.GroupTheory.Claim28503
