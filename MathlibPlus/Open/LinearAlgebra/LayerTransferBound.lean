import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

open scoped BigOperators

noncomputable section

/-- The two-by-two Jacobi transfer matrix from the admitted local recurrence. -/
def jacobiTransferMatrix (a : ℕ → ℝ) (lam : ℝ) (j : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![lam / a (j + 1), -a j / a (j + 1); 1, 0]

/-- The infinity norm of a real two-by-two matrix. -/
def matrixInfinityNorm (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  max (|A 0 0| + |A 0 1|) (|A 1 0| + |A 1 1|)

/-- The ordered product `T_{p + L - 1} ⋯ T_p`. -/
def layerTransfer (T : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => 1
  | L + 1 => T (p + L) * layerTransfer T p L

/-- The local conditioning parameter over the sites in a layer. -/
def localConditioning (a : ℕ → ℝ) (lam c : ℝ) (p q : ℕ) (hpq : p ≤ q) : ℝ :=
  let sites := Finset.Icc p (q + 1)
  max 1 (max (|lam| / c)
    (max
      (sites.sup' (by
        exact ⟨p, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩) (fun r => a r / c))
      (sites.sup' (by
        exact ⟨p, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩) (fun r => c / a r))))

/-- Full layer transfer and inverse bound. -/
def claim9001 : Prop :=
  ∀ (p_N q_N : ℕ) (a_N : ℕ → ℝ) (lam_N c_N : ℝ),
    (hpq : p_N ≤ q_N) →
    0 < c_N →
    (∀ r ∈ Finset.Icc p_N (q_N + 1), 0 < a_N r) →
    let L_N := q_N - p_N + 1
    let 𝒯_N := layerTransfer (jacobiTransferMatrix a_N lam_N) p_N L_N
    max (matrixInfinityNorm 𝒯_N) (matrixInfinityNorm (𝒯_N⁻¹)) ≤
      (2 * (localConditioning a_N lam_N c_N p_N q_N hpq) ^ 2) ^ L_N

end

end MathlibPlus.Open.LinearAlgebra
