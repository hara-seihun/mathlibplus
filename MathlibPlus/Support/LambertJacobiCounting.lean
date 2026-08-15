import Mathlib

namespace MathlibPlus.Support.LambertJacobiCounting

abbrev L2 := ↥(lp (fun _ : ℕ => ℝ) 2)

lemma mem_shift_left (x : L2) :
    Memℓp (fun n : ℕ => x.1 (n + 1)) 2 := by
  have hx : Memℓp x.1 2 := x.2
  unfold Memℓp at hx ⊢
  have h20 : (2 : ENNReal) ≠ 0 := by norm_num
  have h2top : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  simp only [h20, h2top, if_false] at hx ⊢
  have h := (summable_nat_add_iff
      (f := fun n : ℕ => ‖x.1 n‖ ^ (2 : ENNReal).toReal) 1).2 hx
  simpa using h

lemma mem_shift_right (x : L2) :
    Memℓp (fun n : ℕ => if n = 0 then 0 else x.1 (n - 1)) 2 := by
  have hx : Memℓp x.1 2 := x.2
  unfold Memℓp at hx ⊢
  have h20 : (2 : ENNReal) ≠ 0 := by norm_num
  have h2top : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  simp only [h20, h2top, if_false] at hx ⊢
  apply (summable_nat_add_iff
      (f := fun n : ℕ => ‖(if n = 0 then 0 else x.1 (n - 1))‖ ^ (2 : ENNReal).toReal) 1).1
  simpa using hx

def shiftLeftLinear : L2 →ₗ[ℝ] L2 where
  toFun x := ⟨fun n => x.1 (n + 1), mem_shift_left x⟩
  map_add' x y := by
    apply lp.ext
    funext n
    change x.1 (n + 1) + y.1 (n + 1) = x.1 (n + 1) + y.1 (n + 1)
    rfl
  map_smul' c x := by
    apply lp.ext
    funext n
    simp [lp.coeFn_smul, smul_apply]

def shiftRightLinear : L2 →ₗ[ℝ] L2 where
  toFun x := ⟨fun n => if n = 0 then 0 else x.1 (n - 1), mem_shift_right x⟩
  map_add' x y := by
    apply lp.ext
    simp only [lp.coeFn_add]
    funext n
    simp only [PreLp.add_apply, Pi.add_apply]
    by_cases hn : n = 0 <;> simp [hn]
  map_smul' c x := by
    apply lp.ext
    funext n
    by_cases hn : n = 0 <;> simp [hn, lp.coeFn_smul, smul_apply]

lemma norm_shift_left_le (x : L2) :
    ‖shiftLeftLinear x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  let f : ℕ → ℝ := fun n => ‖x.1 n‖ ^ (2 : ENNReal).toReal
  have hfs : Summable f := by
    dsimp [f]
    exact (lp.memℓp x).summable hp
  have hdecomp := hfs.sum_add_tsum_nat_add 1
  have htail : (∑' n : ℕ, f (n + 1)) ≤ ∑' n : ℕ, f n := by
    have hf0 : 0 ≤ f 0 := by
      dsimp [f]
      positivity
    have heq : f 0 + ∑' n : ℕ, f (n + 1) = ∑' n : ℕ, f n := by
      simpa [Finset.sum_range_succ] using hdecomp
    nlinarith
  have hpow := lp.norm_rpow_eq_tsum hp (shiftLeftLinear x)
  have hxpow := lp.norm_rpow_eq_tsum hp x
  have hpow' : ‖shiftLeftLinear x‖ ^ (2 : ENNReal).toReal ≤
      ‖x‖ ^ (2 : ENNReal).toReal := by
    rw [hpow, hxpow]
    exact htail
  have hnonleft : 0 ≤ ‖shiftLeftLinear x‖ := norm_nonneg _
  have hnonx : 0 ≤ ‖x‖ := norm_nonneg _
  norm_num at hpow'
  nlinarith

lemma norm_shift_right_le (x : L2) :
    ‖shiftRightLinear x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  let f : ℕ → ℝ := fun n => ‖x.1 n‖ ^ (2 : ENNReal).toReal
  let g : ℕ → ℝ := fun n => ‖(shiftRightLinear x).1 n‖ ^ (2 : ENNReal).toReal
  have hgs : Summable g := by
    dsimp [g]
    exact (lp.memℓp (shiftRightLinear x)).summable hp
  have hdecomp := hgs.sum_add_tsum_nat_add 1
  have hsum : (∑' n : ℕ, g n) = ∑' n : ℕ, f n := by
    have hdecomp' : g 0 + ∑' n : ℕ, g (n + 1) = ∑' n : ℕ, g n := by
      simpa [Finset.sum_range_succ] using hdecomp
    simpa [f, g, shiftRightLinear, lp.coeFn_add, PreLp.add_apply, Pi.add_apply] using hdecomp'.symm
  have hpow := lp.norm_rpow_eq_tsum hp (shiftRightLinear x)
  have hxpow := lp.norm_rpow_eq_tsum hp x
  have hpow' : ‖shiftRightLinear x‖ ^ (2 : ENNReal).toReal =
      ‖x‖ ^ (2 : ENNReal).toReal := by
    rw [hpow, hxpow]
    exact hsum
  have hnonleft : 0 ≤ ‖shiftRightLinear x‖ := norm_nonneg _
  have hnonx : 0 ≤ ‖x‖ := norm_nonneg _
  norm_num at hpow'
  nlinarith

lemma exists_nonnegative_lambert_root {x : ℝ} (hx : 0 ≤ x) :
    ∃ y : ℝ, y ∈ Set.Icc 0 x ∧ y * Real.exp y = x := by
  let f : ℝ → ℝ := fun y => y * Real.exp y
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) x) :=
    (continuous_id.mul Real.continuous_exp).continuousOn
  have hleft : f 0 ≤ x := by
    dsimp [f]
    simpa using hx
  have hexp : 1 ≤ Real.exp x := by
    have h := Real.add_one_le_exp x
    linarith
  have hright : x ≤ f x := by
    dsimp [f]
    exact le_mul_of_one_le_right hx hexp
  have himage := intermediate_value_Icc hx hf
  have hxmem : x ∈ Set.Icc (f 0) (f x) := ⟨hleft, hright⟩
  rcases himage hxmem with ⟨y, hy, hfy⟩
  exact ⟨y, hy, hfy⟩

noncomputable def lambertW0 (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then Classical.choose (exists_nonnegative_lambert_root hx) else 0

lemma lambertW0_spec {x : ℝ} (hx : 0 ≤ x) :
    lambertW0 x ∈ Set.Icc 0 x ∧ lambertW0 x * Real.exp (lambertW0 x) = x := by
  dsimp [lambertW0]
  rw [dif_pos hx]
  exact Classical.choose_spec (exists_nonnegative_lambert_root hx)

noncomputable def jacobiCoeff (κ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else lambertW0 ((j : ℝ) / κ) / (4 * (j : ℝ))

lemma jacobiCoeff_nonneg {κ : ℝ} (hκ : 0 < κ) (j : ℕ) :
    0 ≤ jacobiCoeff κ j := by
  by_cases hj : j = 0
  · simp [jacobiCoeff, hj]
  · simp only [jacobiCoeff, hj, if_false]
    have hjpos : 0 < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
    have harg : 0 ≤ (j : ℝ) / κ := by positivity
    have hw := (lambertW0_spec harg).1.1
    positivity

lemma jacobiCoeff_bound {κ : ℝ} (hκ : 0 < κ) (j : ℕ) :
    ‖jacobiCoeff κ j‖ ≤ 1 / (4 * κ) := by
  by_cases hj : j = 0
  · simp [jacobiCoeff, hj, hκ.le]
  · simp only [jacobiCoeff, hj, if_false]
    have hjpos : 0 < (j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hj
    have harg : 0 ≤ (j : ℝ) / κ := by positivity
    have hw0 : 0 ≤ lambertW0 ((j : ℝ) / κ) := (lambertW0_spec harg).1.1
    have hw' : lambertW0 ((j : ℝ) / κ) ≤ (j : ℝ) / κ := (lambertW0_spec harg).1.2
    have hden : 0 < 4 * (j : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · apply (div_le_iff₀ hden).2
      calc
        lambertW0 ((j : ℝ) / κ) ≤ (j : ℝ) / κ := hw'
        _ ≤ (1 / (4 * κ)) * (4 * (j : ℝ)) := by
          field_simp
          ring_nf
          norm_num
    · positivity

lemma mem_diagonal (c : ℕ → ℝ) (C : ℝ) (hc : ∀ n, ‖c n‖ ≤ C) (x : L2) :
    Memℓp (fun n => c n * x.1 n) 2 := by
  have hxnorm : Memℓp (fun n : ℕ => ‖x.1 n‖) (2 : ENNReal) := (lp.memℓp x).norm
  have hg : Memℓp (fun n : ℕ => C * ‖x.1 n‖) (2 : ENNReal) := by
    exact Memℓp.const_mul hxnorm C
  refine Memℓp.mono (f := fun n : ℕ => c n * x.1 n) (g := fun n : ℕ => C * ‖x.1 n‖) hg ?_
  intro n
  calc
    ‖c n * x.1 n‖ = ‖c n‖ * ‖x.1 n‖ := norm_mul _ _
    _ ≤ C * ‖x.1 n‖ := mul_le_mul_of_nonneg_right (hc n) (norm_nonneg (x.1 n))

def diagonalLinear (c : ℕ → ℝ) (C : ℝ) (hc : ∀ n, ‖c n‖ ≤ C) : L2 →ₗ[ℝ] L2 where
  toFun x := ⟨fun n => c n * x.1 n, mem_diagonal c C hc x⟩
  map_add' x y := by
    apply lp.ext
    simp only [lp.coeFn_add]
    funext n
    simp only [PreLp.add_apply, Pi.add_apply]
    ring
  map_smul' r x := by
    apply lp.ext
    funext n
    change c n * (r * x.1 n) = r * (c n * x.1 n)
    ring

lemma norm_diagonal_le (c : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) (x : L2) :
    ‖diagonalLinear c C hc x‖ ≤ C * ‖x‖ := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  let y : L2 := diagonalLinear c C hc x
  have hxy : ∀ n : ℕ, ‖y.1 n‖ ≤ C * ‖x.1 n‖ := by
    intro n
    change ‖c n * x.1 n‖ ≤ C * ‖x.1 n‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)
  have hterm : ∀ n : ℕ, y.1 n ^ 2 ≤ (C * x.1 n) ^ 2 := by
    intro n
    apply (sq_le_sq).2
    simpa [y, diagonalLinear, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC] using hxy n
  have hys : Summable (fun n : ℕ => y.1 n ^ 2) := by
    have h := (lp.memℓp y).summable hp
    norm_num at h ⊢
    exact h
  have hxs : Summable (fun n : ℕ => x.1 n ^ 2) := by
    have h := (lp.memℓp x).summable hp
    norm_num at h ⊢
    exact h
  have hupper_s : Summable (fun n : ℕ => (C * x.1 n) ^ 2) := by
    have h := hxs.mul_left (C ^ 2)
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hupper : (∑' n : ℕ, y.1 n ^ 2) ≤
      ∑' n : ℕ, (C * x.1 n) ^ 2 :=
    hys.tsum_le_tsum hterm hupper_s
  have hyNorm := lp.norm_rpow_eq_tsum hp y
  have hxNorm := lp.norm_rpow_eq_tsum hp x
  norm_num at hyNorm hxNorm
  have hsumupper : (∑' n : ℕ, (C * x.1 n) ^ 2) =
      (C * ‖x‖) ^ 2 := by
    calc
      (∑' n : ℕ, (C * x.1 n) ^ 2) =
          ∑' n : ℕ, C ^ 2 * x.1 n ^ 2 := by
            apply tsum_congr
            intro n
            ring
      _ = C ^ 2 * (∑' n : ℕ, x.1 n ^ 2) := tsum_mul_left
      _ = C ^ 2 * ‖x‖ ^ 2 := by rw [← hxNorm]
      _ = (C * ‖x‖) ^ 2 := by ring
  have hpow : ‖y‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    calc
      ‖y‖ ^ 2 = ∑' n : ℕ, y.1 n ^ 2 := hyNorm
      _ ≤ ∑' n : ℕ, (C * x.1 n) ^ 2 := hupper
      _ = (C * ‖x‖) ^ 2 := hsumupper
  have hfinal : ‖y‖ ≤ C * ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).1
    exact hpow
  simpa [y] using hfinal

noncomputable def shiftLeftContinuous : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous shiftLeftLinear 1 (by
    intro x
    simpa using norm_shift_left_le x)

noncomputable def shiftRightContinuous : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous shiftRightLinear 1 (by
    intro x
    simpa using norm_shift_right_le x)

noncomputable def diagonalContinuous (c : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C) : L2 →L[ℝ] L2 :=
  LinearMap.mkContinuous (diagonalLinear c C hc) C (norm_diagonal_le c C hC hc)

noncomputable def jacobiOperatorContinuous (κ : ℝ) (hκ : 0 < κ) : L2 →L[ℝ] L2 :=
  let C : ℝ := 1 / (4 * κ)
  let d₀ : L2 →L[ℝ] L2 :=
    diagonalContinuous (fun n => jacobiCoeff κ n) C (by positivity)
      (fun n => jacobiCoeff_bound hκ n)
  let d₁ : L2 →L[ℝ] L2 :=
    diagonalContinuous (fun n => jacobiCoeff κ (n + 1)) C (by positivity)
      (fun n => jacobiCoeff_bound hκ (n + 1))
  d₀.comp shiftRightContinuous + d₁.comp shiftLeftContinuous

noncomputable def lambertJacobiCount (κ : ℝ) (hκ : 0 < κ) (T : ℝ) : ℕ :=
  Set.ncard {z |
    z ∈ spectrum ℝ (jacobiOperatorContinuous κ hκ) ∧ T⁻¹ < z}

end MathlibPlus.Support.LambertJacobiCounting
