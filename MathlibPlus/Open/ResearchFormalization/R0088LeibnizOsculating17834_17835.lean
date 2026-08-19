import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0088LeibnizOsculating17834_17835

open scoped BigOperators

noncomputable section

/-- The normalized scalar jet coefficient q_k(a). -/
def normalizedScalarJet (q : ℝ → ℝ) (k : ℕ) (a : ℝ) : ℝ :=
  iteratedDeriv k q a / (k.factorial : ℝ)

/-- The upper-triangular normalized Leibniz block. -/
def leibnizBlock (q : ℝ → ℝ) (m : ℕ) (a : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    if i.val ≤ j.val then
      normalizedScalarJet q (j.val - i.val) a
    else 0

/-- Claim 17834: the normalized Leibniz block has determinant q(a)^m,
and every leading block is nonzero when q(a)>0. -/
def claim17834 : Prop :=
  ∀ (q : ℝ → ℝ) (m : ℕ) (a : ℝ),
    Matrix.det (leibnizBlock q m a) = q a ^ m ∧
      (0 < q a →
        ∀ k ≤ m,
          Matrix.det (leibnizBlock q k a) ≠ 0 ∧
            0 < Matrix.det (leibnizBlock q k a))

/-- The normalized vector-valued jet. -/
def normalizedJetVector {d : ℕ}
    (v : ℝ → (Fin d → ℝ)) (k : ℕ) (a : ℝ) : Fin d → ℝ :=
  (k.factorial : ℝ)⁻¹ • iteratedDeriv k v a

/-- The complete osculating subspace through order k. -/
def osculatingSubspace {d : ℕ}
    (v : ℝ → (Fin d → ℝ)) (k : ℕ) (a : ℝ) :
    Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ
    {x | ∃ j < k, x = normalizedJetVector v j a}

/-- Scalar multiplication of a vector-valued curve. -/
def scalarMultiplyCurve {d : ℕ}
    (q : ℝ → ℝ) (v : ℝ → (Fin d → ℝ)) :
    ℝ → (Fin d → ℝ) :=
  fun x => q x • v x

/-- Claim 17835: positive scalar multiplication preserves every initial
osculating subspace under the complete normalized jet carrier. -/
def claim17835 : Prop :=
  ∀ (d m : ℕ) (q : ℝ → ℝ)
    (v : ℝ → (Fin d → ℝ)) (a : ℝ),
    ContDiff ℝ m q →
      ContDiff ℝ m v →
        0 < q a →
          ∀ k ≤ m,
            osculatingSubspace (scalarMultiplyCurve q v) k a =
              osculatingSubspace v k a

end

end MathlibPlus.Open.ResearchFormalization.R0088LeibnizOsculating17834_17835
