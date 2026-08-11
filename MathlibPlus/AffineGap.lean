import Mathlib

/-!
# Positivity from local consecutive-gap tangent orientation

This file formalizes admitted claim 88 with only `C¹` regularity on an interval
containing the knots; no global regularity hypothesis is imposed.
-/

open MeasureTheory

namespace MathlibPlus.AffineGap


/-- The square matrix whose row at `i` is the affine lift `(1, x i)` of a point. -/
def affineSampleMatrix {R : Type*} [One R] {n : ℕ}
    (x : Fin (n + 1) → Fin n → R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i => Fin.cases 1 (fun j => x i j)

/-- Consecutive point differences, one per row. -/
def consecutiveDifferenceMatrix {R : Type*} [Sub R] {n : ℕ}
    (x : Fin (n + 1) → Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => x i.succ j - x i.castSucc j

/-- Successive affine row differences reduce the sampled affine determinant to the
 determinant of the consecutive point differences. -/
theorem det_affineSampleMatrix_eq_det_consecutiveDifference
    {R : Type*} [CommRing R] {n : ℕ} (x : Fin (n + 1) → Fin n → R) :
    Matrix.det (affineSampleMatrix x) = Matrix.det (consecutiveDifferenceMatrix x) := by
  let A := affineSampleMatrix x
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
    Fin.cases (A 0 j) (fun k => A k.succ j - A k.castSucc j) i
  calc
    Matrix.det A = Matrix.det B := by
      apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => (1 : R))
      · intro j
        simp [B]
      · intro i j
        simp [B]
    _ = Matrix.det (consecutiveDifferenceMatrix x) := by
      rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
      · rw [show B 0 0 = 1 by simp [B, A, affineSampleMatrix]]
        simp only [Fin.val_zero, pow_zero, one_mul]
        apply congrArg Matrix.det
        ext i j
        change B i.succ j.succ = x i.succ j - x i.castSucc j
        simp [B, A, affineSampleMatrix]
      · intro i _ hi
        cases i using Fin.cases with
        | zero => exact (hi rfl).elim
        | succ k => simp [B, A, affineSampleMatrix]
      · simp


/-- A determinant whose rows are Bochner integrals is the product-measure
integral of the pointwise row determinant. -/
lemma det_integral_rows_eq_integral_det
    {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → ℝ → Fin n → ℝ)
    (hf : ∀ i j, Integrable (fun x => f i x j) (μ i)) :
    Matrix.det ((fun i j => ∫ x, f i x j ∂μ i) : Matrix (Fin n) (Fin n) ℝ) =
      ∫ x : Fin n → ℝ,
        Matrix.det ((fun i j => f i (x i) j) : Matrix (Fin n) (Fin n) ℝ)
        ∂Measure.pi μ := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j => ∫ x, f i x j ∂μ i
  let B : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun x i j => f i (x i) j
  change Matrix.det A = ∫ x, Matrix.det (B x) ∂Measure.pi μ
  calc
    Matrix.det A = ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i := Matrix.det_apply' A
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ x : Fin n → ℝ,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B x (σ i) i ∂Measure.pi μ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [MeasureTheory.integral_const_mul]
      congr 1
      simp only [A, B]
      calc
        (∏ i, ∫ x, f (σ i) x i ∂μ (σ i)) =
            ∏ i, ∫ x, f i x (σ.symm i) ∂μ i := by
          simpa only [Equiv.symm_apply_apply] using
            (Equiv.prod_comp σ (fun i => ∫ x, f i x (σ.symm i) ∂μ i))
        _ = ∫ x : Fin n → ℝ, ∏ i, f i (x i) (σ.symm i) ∂Measure.pi μ :=
          (MeasureTheory.integral_fintype_prod_eq_prod
            (fun i x => f i x (σ.symm i))).symm
        _ = ∫ x : Fin n → ℝ, ∏ i, f (σ i) (x (σ i)) i ∂Measure.pi μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          symm
          simpa only [Equiv.symm_apply_apply] using
            (Equiv.prod_comp σ (fun i => f i (x i) (σ.symm i)))
    _ = ∫ x : Fin n → ℝ, ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B x (σ i) i ∂Measure.pi μ := by
      rw [MeasureTheory.integral_finsetSum]
      intro σ _
      have hprod : Integrable
          (fun x : Fin n → ℝ => ∏ i, f i (x i) (σ.symm i))
          (Measure.pi μ) :=
        MeasureTheory.Integrable.fintype_prod (fun i => hf i (σ.symm i))
      have heq : (fun x : Fin n → ℝ => ∏ i, B x (σ i) i) =
          (fun x : Fin n → ℝ => ∏ i, f i (x i) (σ.symm i)) := by
        funext x
        simp only [B]
        simpa only [Equiv.symm_apply_apply] using
          (Equiv.prod_comp σ (fun i => f i (x i) (σ.symm i)))
      exact (hprod.congr (Filter.Eventually.of_forall fun x => congrFun heq.symm x)).const_mul _
    _ = ∫ x : Fin n → ℝ, Matrix.det (B x) ∂Measure.pi μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact (Matrix.det_apply' (B x)).symm


/-- If `γ` is `C¹` on a closed interval containing all strictly ordered knots,
and every tangent transversal chosen from the consecutive closed knot gaps has
positive determinant, then the sampled affine determinant is positive. -/
theorem detAffineSampleMatrix_pos
    {n : ℕ} {a b : ℝ} (γ : ℝ → Fin n → ℝ) (q : Fin (n + 1) → ℝ)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hqmem : ∀ i, q i ∈ Set.Icc a b) (hq : StrictMono q)
    (hpos : ∀ s : Fin n → ℝ,
      (∀ i, s i ∈ Set.Icc (q i.castSucc) (q i.succ)) →
      0 < Matrix.det (fun i j => deriv (fun t => γ t j) (s i))) :
    0 < Matrix.det (affineSampleMatrix (fun i => γ (q i))) := by
  rw [det_affineSampleMatrix_eq_det_consecutiveDifference]
  let μ : Fin n → Measure ℝ := fun i =>
    volume.restrict (Set.Ioc (q i.castSucc) (q i.succ))
  let T : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun s i j =>
    deriv (fun t => γ t j) (s i)
  have hcoord (j : Fin n) :
      ContDiffOn ℝ 1 (fun t => γ t j) (Set.Icc a b) := by
    convert (contDiff_apply ℝ ℝ j).comp_contDiffOn hγ using 1
    rfl
  have hlocal (i j : Fin n) :
      ContDiffOn ℝ 1 (fun t => γ t j)
        (Set.Icc (q i.castSucc) (q i.succ)) :=
    (hcoord j).mono (Set.Icc_subset_Icc (hqmem i.castSucc).1 (hqmem i.succ).2)
  have hentry (i j : Fin n) :
      consecutiveDifferenceMatrix (fun k => γ (q k)) i j =
        ∫ s, deriv (fun t => γ t j) s ∂μ i := by
    change γ (q i.succ) j - γ (q i.castSucc) j =
      ∫ s, deriv (fun t => γ t j) s ∂μ i
    rw [← intervalIntegral.integral_of_le (hq i.castSucc_lt_succ).le]
    exact (intervalIntegral.integral_deriv_of_contDiffOn_Icc
      (hlocal i j) (hq i.castSucc_lt_succ).le).symm
  have hf (i j : Fin n) :
      Integrable (fun s => deriv (fun t => γ t j) s) (μ i) := by
    have hlt : q i.castSucc < q i.succ := hq i.castSucc_lt_succ
    have hwithin : IntervalIntegrable
        (derivWithin (fun t => γ t j) (Set.Icc (q i.castSucc) (q i.succ)))
        volume (q i.castSucc) (q i.succ) :=
      ((hlocal i j).derivWithin (m := 0) (uniqueDiffOn_Icc hlt) (by simp)).continuousOn
        |>.intervalIntegrable_of_Icc hlt.le
    have hglobal : IntervalIntegrable (deriv (fun t => γ t j))
        volume (q i.castSucc) (q i.succ) := by
      apply hwithin.congr_ae
      simp only [Set.uIoc_of_le hlt.le]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
    change IntegrableOn (deriv (fun t => γ t j))
      (Set.Ioc (q i.castSucc) (q i.succ)) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).mp hglobal
  have hdet : Matrix.det
      (consecutiveDifferenceMatrix (fun k => γ (q k))) =
      ∫ s : Fin n → ℝ, Matrix.det (T s) ∂Measure.pi μ := by
    calc
      Matrix.det (consecutiveDifferenceMatrix (fun k => γ (q k))) =
          Matrix.det ((fun i j => ∫ s, deriv (fun t => γ t j) s ∂μ i) :
            Matrix (Fin n) (Fin n) ℝ) := by
        congr 1
        ext i j
        exact hentry i j
      _ = ∫ s : Fin n → ℝ, Matrix.det (T s) ∂Measure.pi μ := by
        simpa only [T] using det_integral_rows_eq_integral_det μ
          (fun _ s j => deriv (fun t => γ t j) s) hf
  rw [hdet]
  have hTIntegrable : Integrable (fun s : Fin n → ℝ => Matrix.det (T s))
      (Measure.pi μ) := by
    classical
    rw [show (fun s : Fin n → ℝ => Matrix.det (T s)) =
        (fun s => ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, T s (σ i) i) by
      funext s
      exact Matrix.det_apply' (T s)]
    apply integrable_finsetSum Finset.univ
    intro σ _
    have hprod : Integrable
        (fun s : Fin n → ℝ =>
          ∏ i, deriv (fun t => γ t (σ.symm i)) (s i))
        (Measure.pi μ) :=
      MeasureTheory.Integrable.fintype_prod (fun i => hf i (σ.symm i))
    have heq :
        (fun s : Fin n → ℝ => ∏ i, T s (σ i) i) =
        (fun s : Fin n → ℝ =>
          ∏ i, deriv (fun t => γ t (σ.symm i)) (s i)) := by
      funext s
      simp only [T]
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.prod_comp σ
          (fun i => deriv (fun t => γ t (σ.symm i)) (s i)))
    exact (hprod.congr
      (Filter.Eventually.of_forall fun s => congrFun heq.symm s)).const_mul _
  have hbox : ∀ᵐ s : Fin n → ℝ ∂Measure.pi μ,
      ∀ i, s i ∈ Set.Ioc (q i.castSucc) (q i.succ) := by
    rw [Filter.eventually_all]
    intro i
    apply Measure.tendsto_eval_ae_ae.eventually
    simpa only [μ] using
      (ae_restrict_mem (μ := volume)
        (measurableSet_Ioc : MeasurableSet (Set.Ioc (q i.castSucc) (q i.succ))))
  have hpositive : ∀ᵐ s : Fin n → ℝ ∂Measure.pi μ, 0 < Matrix.det (T s) :=
    hbox.mono fun s hs => hpos s fun i =>
      ⟨(hs i).1.le, (hs i).2⟩
  rw [(integral_pos_iff_support_of_nonneg_ae
    (hpositive.mono fun _ hs => hs.le) hTIntegrable)]
  have hsupp : Function.support (fun s : Fin n → ℝ => Matrix.det (T s))
      =ᵐ[Measure.pi μ] Set.univ := hpositive.mono fun s hs => by
    change (Matrix.det (T s) ≠ 0) = (s ∈ Set.univ)
    apply propext
    simp only [Set.mem_univ, iff_true]
    exact hs.ne'
  rw [measure_congr hsupp, Measure.pi_univ, pos_iff_ne_zero]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  simp only [μ, Measure.restrict_apply_univ, Real.volume_Ioc]
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hq i.castSucc_lt_succ))).ne'

end MathlibPlus.AffineGap
