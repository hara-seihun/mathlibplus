import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The affine metric pencil `A(b) = A₀ + (b - b₀) S`. -/
def affineMetricPencil {n : ℕ} (A₀ S : Matrix (Fin n) (Fin n) ℝ)
    (b₀ b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A₀ + (b - b₀) • S

/-- The leading principal section of order `k + 1`. -/
def leadingSection {n : ℕ} (k : Fin n) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) ℝ :=
  A.submatrix (Fin.castLE (Nat.succ_le_of_lt k.isLt))
    (Fin.castLE (Nat.succ_le_of_lt k.isLt))

/-- The leading principal sections of an affine metric pencil. -/
def leadingMetricPencil {n : ℕ} (A₀ S : Matrix (Fin n) (Fin n) ℝ)
    (b₀ b : ℝ) (k : Fin n) : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) ℝ :=
  leadingSection k (affineMetricPencil A₀ S b₀ b)

/-- The inverse square root of a real symmetric matrix, via its Hermitian functional calculus. -/
noncomputable def inverseSquareRoot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) : Matrix (Fin n) (Fin n) ℝ :=
  ((Matrix.isHermitian_iff_isSymm).2 hA).cfc (fun x : ℝ => x ^ (-1 / 2 : ℝ))

/-- The spectral (ℓ² operator) norm of a real square matrix. -/
noncomputable def spectralNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- A full whitened slope. -/
noncomputable def whitenedSlope {n : ℕ} (A₀ S : Matrix (Fin n) (Fin n) ℝ)
    (hA₀ : A₀.IsSymm) : Matrix (Fin n) (Fin n) ℝ :=
  inverseSquareRoot A₀ hA₀ * S * inverseSquareRoot A₀ hA₀

/--
Norm inheritance by leading sections: for real symmetric rank-`n` affine metric pencils with
positive-definite canonical endpoints, every leading relative slope has spectral norm at most that
of the full whitened slope, for both pencils.
-/
def norm_inheritance_leading_sections : Prop :=
  ∀ (n : ℕ) (b₀ : ℝ)
    (N₀ S_N M₀ S_M : Matrix (Fin n) (Fin n) ℝ),
    ∀ (hN₀ : N₀.IsSymm) (hS_N : S_N.IsSymm)
      (hM₀ : M₀.IsSymm) (hS_M : S_M.IsSymm)
      (_hN₀_pos : N₀.PosDef) (_hM₀_pos : M₀.PosDef),
    ∀ k : Fin n,
      let N_k := fun b : ℝ => leadingMetricPencil N₀ S_N b₀ b k
      let M_k := fun b : ℝ => leadingMetricPencil M₀ S_M b₀ b k
      let hN_k : (N_k b₀).IsSymm := by
        dsimp [N_k, leadingMetricPencil, affineMetricPencil, leadingSection]
        exact (hN₀.add (hS_N.smul (b₀ - b₀))).submatrix
          (Fin.castLE (Nat.succ_le_of_lt k.isLt))
      let hM_k : (M_k b₀).IsSymm := by
        dsimp [M_k, leadingMetricPencil, affineMetricPencil, leadingSection]
        exact (hM₀.add (hS_M.smul (b₀ - b₀))).submatrix
          (Fin.castLE (Nat.succ_le_of_lt k.isLt))
      let A_N := whitenedSlope N₀ S_N hN₀
      let A_M := whitenedSlope M₀ S_M hM₀
      spectralNorm
          (inverseSquareRoot (N_k b₀) hN_k * leadingSection k S_N *
            inverseSquareRoot (N_k b₀) hN_k) ≤ spectralNorm A_N ∧
        spectralNorm
          (inverseSquareRoot (M_k b₀) hM_k * leadingSection k S_M *
            inverseSquareRoot (M_k b₀) hM_k) ≤ spectralNorm A_M

end MathlibPlus.Open.Analysis
