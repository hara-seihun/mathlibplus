import Mathlib

open scoped MatrixOrder

namespace MathlibPlus.Open.Analysis

/-- The operator norm on the Euclidean space of real `n`-vectors. -/
noncomputable def spectralTwoNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((Matrix.toEuclideanLin A).toContinuousLinearMap).opNorm

/-- Congruence by the inverse positive square root of a positive matrix. -/
noncomputable def whitenedSlope {n : ℕ}
    (P S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (CFC.sqrt P)⁻¹ * S * (CFC.sqrt P)⁻¹

/-- The affine pencil with canonical value `P` at `b₀`. -/
def affinePencil {n : ℕ}
    (P S : Matrix (Fin n) (Fin n) ℝ) (b₀ b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  P + (b - b₀) • S

/-- The leading `k` by `k` principal section of an `n` by `n` matrix. -/
def leadingSection {n k : ℕ} (hk : k ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => A ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ ⟨j.val, lt_of_lt_of_le j.isLt hk⟩

/-- The determinant of a leading section of an affine pencil. -/
noncomputable def sectionDet {n : ℕ}
    (P S : Matrix (Fin n) (Fin n) ℝ) (b₀ b : ℝ) (k : ℕ) (hk : k ≤ n) : ℝ :=
  Matrix.det (leadingSection hk (affinePencil P S b₀ b))

/-- The positive determinant-ratio coefficient `r_j`. -/
noncomputable def rCoeff {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ) (b₀ b : ℝ)
    (j : ℕ) (hj : j + 1 ≤ n) : ℝ :=
  let hj₀ : j ≤ n := Nat.le_trans (Nat.le_succ j) hj
  Real.sqrt ((sectionDet M₀ S_M b₀ b (j + 1) hj *
      sectionDet N₀ S_N b₀ b j hj₀) /
    (sectionDet N₀ S_N b₀ b (j + 1) hj *
      sectionDet M₀ S_M b₀ b j hj₀))

/-- The positive determinant-ratio coefficient `s_j`. -/
noncomputable def sCoeff {n : ℕ}
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ) (b₀ b : ℝ)
    (j : ℕ) (h₁j : 1 ≤ j) (hj : j + 1 ≤ n) : ℝ :=
  let hj₀ : j ≤ n := Nat.le_trans (Nat.le_succ j) hj
  let hjminus : j - 1 ≤ n := Nat.le_trans (Nat.sub_le j 1) hj₀
  Real.sqrt ((sectionDet N₀ S_N b₀ b (j + 1) hj *
      sectionDet M₀ S_M b₀ b (j - 1) hjminus) /
    (sectionDet N₀ S_N b₀ b j hj₀ *
      sectionDet M₀ S_M b₀ b j hj₀))

/--
Transport of the two adjacent parity/free-energy defects.  The coefficients are
those supplied by the determinant identities for the interlaced sequence
`(r₀,s₁,r₁,…,s_{n-1},r_{n-1})`.
-/
def adjacentDefectTransport : Prop :=
  ∀ (n : ℕ) (b₀ Δ : ℝ)
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ),
    N₀.IsSymm → M₀.IsSymm → S_N.IsSymm → S_M.IsSymm →
    N₀.PosDef → M₀.PosDef →
    let A_N := whitenedSlope N₀ S_N
    let A_M := whitenedSlope M₀ S_M
    let L := max (spectralTwoNorm A_N) (spectralTwoNorm A_M)
    let η := Δ * L
    let ℒη := -Real.log (1 - η)
    η < 1 →
    ∀ b, |b - b₀| ≤ Δ →
      ∀ (j : ℕ) (h₁j : 1 ≤ j) (hj : j + 1 ≤ n),
        let hprev : (j - 1) + 1 ≤ n := by omega
        let rprev := rCoeff N₀ M₀ S_N S_M b₀ b (j - 1) hprev
        let rprev₀ := rCoeff N₀ M₀ S_N S_M b₀ b₀ (j - 1) hprev
        let sj := sCoeff N₀ M₀ S_N S_M b₀ b j h₁j hj
        let sj₀ := sCoeff N₀ M₀ S_N S_M b₀ b₀ j h₁j hj
        let rj := rCoeff N₀ M₀ S_N S_M b₀ b j hj
        let rj₀ := rCoeff N₀ M₀ S_N S_M b₀ b₀ j hj
        |Real.log (rprev / sj) - Real.log (rprev₀ / sj₀)| ≤
            (4 * (j : ℝ) - 1) * ℒη ∧
        |Real.log (sj / rj) - Real.log (sj₀ / rj₀)| ≤
            (4 * (j : ℝ) + 1) * ℒη

end MathlibPlus.Open.Analysis
