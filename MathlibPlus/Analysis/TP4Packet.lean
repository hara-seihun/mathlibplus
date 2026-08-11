import Mathlib

namespace MathlibPlus.Analysis.TP4Packet

/-- The one-shell function used in the rank-four packet. -/
noncomputable def packetFunction (n : ℕ) (l : ℝ) : ℝ :=
  l ^ (-(1 : ℝ) / 4) *
      (Real.exp (-Real.pi * (n : ℝ) ^ 2 / l) -
        Real.exp (-Real.pi * (n + 1 : ℕ) ^ 2 / l)) +
    l ^ ((1 : ℝ) / 4) *
      (Real.exp (-Real.pi * (n : ℝ) ^ 2 * l) -
        Real.exp (-Real.pi * (n + 1 : ℕ) ^ 2 * l))

/-- Exponential reflection of the packet function. -/
theorem reflection (n : ℕ) (t : ℝ) :
    packetFunction n (Real.exp (-t)) = packetFunction n (Real.exp t) := by
  rw [packetFunction, packetFunction]
  simp only [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [Real.exp_neg]
  simp only [div_inv_eq_mul]
  ring_nf

/-- The packet function in logarithmic scale. -/
noncomputable def exponentialPacket (n : ℕ) (t : ℝ) : ℝ :=
  packetFunction n (Real.exp t)

/-- Reflection makes the logarithmic-scale packet function even. -/
theorem exponentialPacket_even (n : ℕ) : Function.Even (exponentialPacket n) := by
  intro t
  exact reflection n t

/-- Successive derivatives of an even real function alternate parity. -/
theorem iteratedDeriv_even_parity {f : ℝ → ℝ} (hf : Function.Even f) (k : ℕ) (t : ℝ) :
    iteratedDeriv k f (-t) = (-1 : ℝ) ^ k * iteratedDeriv k f t := by
  have hfun : (fun x : ℝ ↦ f (-x)) = f := funext hf
  calc
    iteratedDeriv k f (-t) = iteratedDeriv k (fun x : ℝ ↦ f (-x)) (-t) := by rw [hfun]
    _ = (-1 : ℝ) ^ k * iteratedDeriv k f t := by
      simpa only [neg_neg, smul_eq_mul] using iteratedDeriv_comp_neg k f (-t)

/-- The logarithmic derivatives of each packet function alternate parity. -/
theorem exponentialPacket_iteratedDeriv_parity (n k : ℕ) (t : ℝ) :
    iteratedDeriv k (exponentialPacket n) (-t) =
      (-1 : ℝ) ^ k * iteratedDeriv k (exponentialPacket n) t :=
  iteratedDeriv_even_parity (exponentialPacket_even n) k t

/-- The `4 × 4` packet jet matrix with derivative orders `0,1,2,3`. -/
noncomputable def jetMatrix (indices : Fin 4 → ℕ) (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ iteratedDeriv j.1 (exponentialPacket (indices i)) t

/-- The rank-four packet determinant. -/
noncomputable def packetDeterminant (indices : Fin 4 → ℕ) (t : ℝ) : ℝ :=
  (jetMatrix indices t).det

/-- The rank-four packet determinant is even in logarithmic scale. -/
theorem packetDeterminant_even (indices : Fin 4 → ℕ) :
    Function.Even (packetDeterminant indices) := by
  intro t
  rw [packetDeterminant, packetDeterminant]
  have hmatrix :
      jetMatrix indices (-t) =
        Matrix.of (fun i j ↦ (-1 : ℝ) ^ j.1 * jetMatrix indices t i j) := by
    ext i j
    exact exponentialPacket_iteratedDeriv_parity (indices i) j.1 t
  rw [hmatrix, Matrix.det_mul_row]
  norm_num [Fin.prod_univ_four]

/-- At the reflection point, the odd-derivative columns of the packet jet vanish. -/
theorem oddDerivativeColumns_zero (indices : Fin 4 → ℕ) :
    (∀ i, jetMatrix indices 0 i (1 : Fin 4) = 0) ∧
      ∀ i, jetMatrix indices 0 i (3 : Fin 4) = 0 := by
  constructor
  · intro i
    have h := exponentialPacket_iteratedDeriv_parity (indices i) 1 0
    simp [jetMatrix] at h ⊢
    linarith
  · intro i
    have h := exponentialPacket_iteratedDeriv_parity (indices i) 3 0
    simp [jetMatrix] at h ⊢
    linarith

end MathlibPlus.Analysis.TP4Packet
