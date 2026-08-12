import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

open scoped Matrix ENNReal NNReal

namespace MathlibPlus.LinearAlgebra

/-- Claim 53173: the reciprocal endpoint two-cycle, its majorant obstruction,
and the persistence of that obstruction for block-upper-triangular extensions. -/
theorem reciprocalEndpointCycle_claim53173 {K N : ℝ} (hK : 0 < K) (hKN : K < N) :
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![
      0, Real.sqrt (N / K);
      Real.sqrt (K / N), 0]
    J * J = 1 ∧
      |J 0 1| * |J 1 0| = 1 ∧
      (∀ A : Matrix (Fin 2) (Fin 2) ℝ,
        (∀ i j, 0 ≤ A i j ∧ |J i j| ≤ A i j) →
          1 ≤ spectralRadius ℝ A) ∧
      (∀ (m : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ)
          (B : Matrix (Fin 2) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ),
        (∀ i j, 0 ≤ A i j ∧ |J i j| ≤ A i j) →
          1 ≤ spectralRadius ℝ (Matrix.fromBlocks A B 0 D)) := by
  dsimp
  have hN : 0 < N := lt_trans hK hKN
  have hNK : 0 < N / K := div_pos hN hK
  have hKNpos : 0 < K / N := div_pos hK hN
  have hsNK : (Real.sqrt (N / K)) ^ 2 = N / K := by
    rw [Real.sq_sqrt (le_of_lt hNK)]
  have hsKN : (Real.sqrt (K / N)) ^ 2 = K / N := by
    rw [Real.sq_sqrt (le_of_lt hKNpos)]
  have hprod : Real.sqrt (N / K) * Real.sqrt (K / N) = 1 := by
    rw [← Real.sqrt_mul (le_of_lt hNK)]
    field_simp
    norm_num
  have hprod' : Real.sqrt (K / N) * Real.sqrt (N / K) = 1 := by
    simpa [mul_comm] using hprod
  have root_witness :
      ∀ (A : Matrix (Fin 2) (Fin 2) ℝ),
        (∀ i j, 0 ≤ A i j ∧
          |(!![0, Real.sqrt (N / K); Real.sqrt (K / N), 0] :
            Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ A i j) →
        ∃ lam : ℝ, 1 ≤ lam ∧
          (lam - A 0 0) * (lam - A 1 1) - A 0 1 * A 1 0 = 0 := by
    intro A hA
    let a : ℝ := A 0 0
    let b : ℝ := A 0 1
    let c : ℝ := A 1 0
    let d : ℝ := A 1 1
    have ha : 0 ≤ a := by
      dsimp [a]
      exact (hA 0 0).1
    have hb : 0 ≤ b := by
      dsimp [b]
      exact (hA 0 1).1
    have hc : 0 ≤ c := by
      dsimp [c]
      exact (hA 1 0).1
    have hd : 0 ≤ d := by
      dsimp [d]
      exact (hA 1 1).1
    have hsb : Real.sqrt (N / K) ≤ b := by
      dsimp [b]
      simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using (hA 0 1).2
    have hsc : Real.sqrt (K / N) ≤ c := by
      dsimp [c]
      simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using (hA 1 0).2
    have hbc' : Real.sqrt (N / K) * Real.sqrt (K / N) ≤ b * c := by
      exact mul_le_mul hsb hsc (Real.sqrt_nonneg _) hb
    have hbc : 1 ≤ b * c := by
      nlinarith [hbc', hprod]
    let q : ℝ := Real.sqrt ((a - d) ^ 2 + 4 * b * c)
    let lam : ℝ := (a + d + q) / 2
    have hdisc : 0 ≤ (a - d) ^ 2 + 4 * b * c := by positivity
    have hq2 : q ^ 2 = (a - d) ^ 2 + 4 * b * c := by
      dsimp [q]
      exact Real.sq_sqrt hdisc
    have hq : 2 ≤ q := by
      have hqnonneg : 0 ≤ q := by
        dsimp [q]
        exact Real.sqrt_nonneg _
      nlinarith
    have hlam : 1 ≤ lam := by
      dsimp [lam]
      nlinarith
    have hroot : (lam - a) * (lam - d) - b * c = 0 := by
      dsimp [lam]
      nlinarith [hq2]
    refine ⟨lam, hlam, ?_⟩
    simpa [a, b, c, d] using hroot
  have hmajorant :
      ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
        (∀ i j, 0 ≤ A i j ∧
          |(!![0, Real.sqrt (N / K); Real.sqrt (K / N), 0] :
            Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ A i j) →
          1 ≤ spectralRadius ℝ A := by
    intro A hA
    obtain ⟨lam, hlam, hroot⟩ := root_witness A hA
    have hspec : lam ∈ spectrum ℝ A := by
      apply Matrix.mem_spectrum_of_isRoot_charpoly
      rw [Polynomial.IsRoot.def]
      simp [Matrix.charpoly, Matrix.det_fin_two]
      exact hroot
    have hnorm : (1 : ℝ≥0∞) ≤ (‖lam‖₊ : ℝ≥0∞) := by
      have hlamnorm : (1 : ℝ) ≤ ‖lam‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        exact hlam
      exact_mod_cast hlamnorm
    have hspecbound : (‖lam‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ A := by
      exact le_iSup₂ (α := ℝ≥0∞) lam hspec
    exact hnorm.trans hspecbound
  have hblock :
      ∀ (m : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ)
          (B : Matrix (Fin 2) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ),
        (∀ i j, 0 ≤ A i j ∧
          |(!![0, Real.sqrt (N / K); Real.sqrt (K / N), 0] :
            Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ A i j) →
          1 ≤ spectralRadius ℝ (Matrix.fromBlocks A B 0 D) := by
    intro m A B D hA
    obtain ⟨lam, hlam, hroot⟩ := root_witness A hA
    have hspec : lam ∈ spectrum ℝ (Matrix.fromBlocks A B 0 D) := by
      apply Matrix.mem_spectrum_of_isRoot_charpoly
      rw [Polynomial.IsRoot.def, Matrix.charpoly_fromBlocks_zero₂₁,
        Polynomial.eval_mul]
      have hroot' : A.charpoly.eval lam = 0 := by
        simp [Matrix.charpoly, Matrix.det_fin_two]
        exact hroot
      rw [hroot']
      simp
    have hnorm : (1 : ℝ≥0∞) ≤ (‖lam‖₊ : ℝ≥0∞) := by
      have hlamnorm : (1 : ℝ) ≤ ‖lam‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        exact hlam
      exact_mod_cast hlamnorm
    have hspecbound :
        (‖lam‖₊ : ℝ≥0∞) ≤
          spectralRadius ℝ (Matrix.fromBlocks A B 0 D) := by
      exact le_iSup₂ (α := ℝ≥0∞) lam hspec
    exact hnorm.trans hspecbound
  refine ⟨?_, ?_, hmajorant, hblock⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hsNK, hsKN, hprod, hprod',
        mul_comm]
  · rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hprod

end MathlibPlus.LinearAlgebra
