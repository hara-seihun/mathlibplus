import Mathlib

namespace MathlibPlus.Analysis

private def W (m : ℕ) (t a b : ℝ) : ℝ := t ^ m * a * b

private noncomputable def hessW (m : ℕ) (t a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![
    deriv (fun x => deriv (fun y => W m t y b) x) a,
    deriv (fun x => deriv (fun y => W m t x y) b) a;
    deriv (fun x => deriv (fun y => W m t y x) a) b,
    deriv (fun x => deriv (fun y => W m t a y) x) b]

private theorem deriv_W_left (m : ℕ) (t b x : ℝ) :
    deriv (fun y => W m t y b) x = t ^ m * b := by
  have h := ((hasDerivAt_const x (t ^ m)).mul (hasDerivAt_id x)).mul_const b
  convert h.deriv using 1 <;> simp [W, id]

private theorem deriv_W_right (m : ℕ) (t a x : ℝ) :
    deriv (fun y => W m t a y) x = t ^ m * a := by
  have h := (hasDerivAt_const x (t ^ m * a)).mul (hasDerivAt_id x)
  convert h.deriv using 1 <;> simp [W, id]

private theorem hessW_eq (m : ℕ) (t a b : ℝ) :
    hessW m t a b = !![0, t ^ m; t ^ m, 0] := by
  funext i j
  fin_cases i <;> fin_cases j
  · simp only [hessW, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (fun x => deriv (fun y => W m t y b) x) = (fun _ => t ^ m * b) by
      funext x; exact deriv_W_left m t b x]
    simp
  · simp only [hessW, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (fun x => deriv (fun y => W m t x y) b) = (fun x => t ^ m * x) by
      funext x; exact deriv_W_right m t x b]
    have h := ((hasDerivAt_const a (t ^ m)).mul (hasDerivAt_id a)).deriv
    convert h using 1 <;> simp [id]
  · simp only [hessW, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (fun x => deriv (fun y => W m t y x) a) = (fun x => t ^ m * x) by
      funext x; exact deriv_W_left m t x a]
    have h := ((hasDerivAt_const b (t ^ m)).mul (hasDerivAt_id b)).deriv
    convert h using 1 <;> simp [id]
  · simp only [hessW, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (fun x => deriv (fun y => W m t a y) x) = (fun _ => t ^ m * a) by
      funext x; exact deriv_W_right m t a x]
    simp

end MathlibPlus.Analysis

namespace MathlibPlus.Open.Analysis

def bilinearSelfDualPotentialDoublesZeroOrder : Prop :=
  ∀ (m : ℕ) (t a b : ℝ),
    let W : ℝ → ℝ → ℝ := fun x y => t ^ m * x * y
    let H : Matrix (Fin 2) (Fin 2) ℝ :=
      !![
        deriv (fun x => deriv (fun y => W y b) x) a,
        deriv (fun x => deriv (fun y => W x y) b) a;
        deriv (fun x => deriv (fun y => W y x) a) b,
        deriv (fun x => deriv (fun y => W a y) x) b]
    let oneSided : Matrix (Fin 1) (Fin 1) ℝ := !![H 0 1]
    let zeroH : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 0]
    let criticalH : Matrix (Fin 2) (Fin 2) ℝ :=
      !![
        deriv (fun x => deriv (fun y => (0 : ℝ) ^ m * y * b) x) a,
        deriv (fun x => deriv (fun y => (0 : ℝ) ^ m * x * y) b) a;
        deriv (fun x => deriv (fun y => (0 : ℝ) ^ m * y * x) a) b,
        deriv (fun x => deriv (fun y => (0 : ℝ) ^ m * a * y) x) b]
    H = !![0, t ^ m; t ^ m, 0] ∧
      H.det = -(t ^ (2 * m)) ∧
      H.transpose = H ∧
      Polynomial.rootMultiplicity (0 : ℝ) ((Polynomial.X : Polynomial ℝ) ^ m) = m ∧
      Polynomial.rootMultiplicity (0 : ℝ) (-((Polynomial.X : Polynomial ℝ) ^ (2 * m))) = 2 * m ∧
      oneSided.det = t ^ m ∧
      (0 < m →
        criticalH = zeroH ∧
        (∃ u : Fin 2 → ℝ, u ≠ 0 ∧ zeroH.mulVec u = 0) ∧
        (∃ v : Fin 2 → ℝ, v ≠ 0 ∧ zeroH.transpose.mulVec v = 0) ∧
        ¬ Function.Injective zeroH.mulVec ∧
        ¬ Function.Surjective zeroH.mulVec)

end MathlibPlus.Open.Analysis

namespace MathlibPlus.Analysis

theorem bilinearSelfDualPotentialDoublesZeroOrder_proved :
    MathlibPlus.Open.Analysis.bilinearSelfDualPotentialDoublesZeroOrder := by
  dsimp [MathlibPlus.Open.Analysis.bilinearSelfDualPotentialDoublesZeroOrder]
  intro m t a b
  change
    hessW m t a b = !![0, t ^ m; t ^ m, 0] ∧
      (hessW m t a b).det = -(t ^ (2 * m)) ∧
      (hessW m t a b).transpose = hessW m t a b ∧
      Polynomial.rootMultiplicity (0 : ℝ) ((Polynomial.X : Polynomial ℝ) ^ m) = m ∧
      Polynomial.rootMultiplicity (0 : ℝ) (-((Polynomial.X : Polynomial ℝ) ^ (2 * m))) = 2 * m ∧
      (!![(hessW m t a b) 0 1] : Matrix (Fin 1) (Fin 1) ℝ).det = t ^ m ∧
      (0 < m →
        hessW m 0 a b = !![0, 0; 0, 0] ∧
        (∃ u : Fin 2 → ℝ, u ≠ 0 ∧
          (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec u = 0) ∧
        (∃ v : Fin 2 → ℝ, v ≠ 0 ∧
          (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).transpose.mulVec v = 0) ∧
        ¬ Function.Injective ((!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec) ∧
        ¬ Function.Surjective ((!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec))
  have hH : hessW m t a b = !![0, t ^ m; t ^ m, 0] := hessW_eq m t a b
  have hdet : (hessW m t a b).det = -(t ^ (2 * m)) := by
    rw [hH, Matrix.det_fin_two]
    norm_num
    ring
  have hsym : (hessW m t a b).transpose = hessW m t a b := by
    rw [hH]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hp : Polynomial.rootMultiplicity (0 : ℝ) (Polynomial.X ^ m) = m := by
    simpa using (Polynomial.rootMultiplicity_X_sub_C_pow (0 : ℝ) m)
  have hd : Polynomial.rootMultiplicity (0 : ℝ) (-(Polynomial.X ^ (2 * m))) = 2 * m := by
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
    simp
  have hone :
      (!![(hessW m t a b) 0 1] : Matrix (Fin 1) (Fin 1) ℝ).det = t ^ m := by
    rw [Matrix.det_fin_one]
    rw [hH]
    rfl
  refine ⟨hH, hdet, hsym, hp, hd, hone, ?_⟩
  intro hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hessW_eq]
    simp [zero_pow (Nat.ne_of_gt hm)]
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp at h0
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp at h0
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro hinj
    have hzero :
        ((!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec (![1, 0])) =
          (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVec 0 := by
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hne : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simp at h0
    exact hne (hinj hzero)
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj ![1, 0]
    have hx0 := congrFun hx 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hx0

end MathlibPlus.Analysis
