import Mathlib

namespace MathlibPlus.LinearAlgebra

section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The projection onto the fixed space of an involution, written in the
sandwich form used by the compression identity. -/
def projection_claim10967 (D : Module.End ℚ V) : Module.End ℚ V :=
  (1 / 2 : ℚ) • (1 + D)

/-- The first-kind Chebyshev recurrence, evaluated in an endomorphism ring. -/
def chebyshevFirstKind_claim10967 (A : Module.End ℚ V) : ℕ → Module.End ℚ V
  | 0 => 1
  | 1 => A
  | n + 2 =>
      A * chebyshevFirstKind_claim10967 A (n + 1) +
        A * chebyshevFirstKind_claim10967 A (n + 1) -
        chebyshevFirstKind_claim10967 A n

theorem inversionCompression_claim10967
    (T D Tinv : Module.End ℚ V)
    (hD : D * D = 1)
    (_hT : T * Tinv = 1)
    (hTinv : Tinv * T = 1)
    (hconj : D * T * D = Tinv) :
    let P := projection_claim10967 D
    let A := P * T * P
    A = (1 / 2 : ℚ) • (T + Tinv) * P ∧
      ∀ n : ℕ, P * T ^ n * P =
        chebyshevFirstKind_claim10967 A n * P := by
  dsimp only
  let P : Module.End ℚ V := projection_claim10967 D
  let A : Module.End ℚ V := P * T * P
  change A = (1 / 2 : ℚ) • (T + Tinv) * P ∧
    ∀ n : ℕ, P * T ^ n * P =
      chebyshevFirstKind_claim10967 A n * P
  have hDT : D * T = Tinv * D := by
    calc
      D * T = D * T * (D * D) := by rw [hD]; simp
      _ = (D * T * D) * D := by simp [mul_assoc]
      _ = Tinv * D := by rw [hconj]
  have hconj' : D * Tinv * D = T := by
    calc
      D * Tinv * D = D * (D * T * D) * D := by rw [hconj]
      _ = (D * D) * T * (D * D) := by noncomm_ring
      _ = T := by rw [hD]; simp
  have hDTinv : D * Tinv = T * D := by
    calc
      D * Tinv = D * Tinv * (D * D) := by rw [hD]; simp
      _ = (D * Tinv * D) * D := by simp [mul_assoc]
      _ = T * D := by rw [hconj']
  have hP : P * P = P := by
    dsimp [P, projection_claim10967]
    noncomm_ring
    norm_num [smul_add, add_smul, smul_smul, hD]
    module
  have hSP : (T + Tinv) * P = P * (T + Tinv) := by
    have hSD : (T + Tinv) * D = D * (T + Tinv) := by
      calc
        (T + Tinv) * D = T * D + Tinv * D := by rw [add_mul]
        _ = D * Tinv + D * T := by rw [← hDTinv, ← hDT]
        _ = D * (T + Tinv) := by rw [mul_add, add_comm]
    dsimp [P, projection_claim10967]
    ext v
    simp [Module.End.mul_apply]
    have h1 : D (T v) = Tinv (D v) := by
      have h := congrArg (fun f : Module.End ℚ V => f v) hDT
      simpa [Module.End.mul_apply] using h
    have h2 : D (Tinv v) = T (D v) := by
      have h := congrArg (fun f : Module.End ℚ V => f v) hDTinv
      simpa [Module.End.mul_apply] using h
    rw [h1, h2]
    module
  have hA : A = (1 / 2 : ℚ) • (T + Tinv) * P := by
    dsimp [A, P, projection_claim10967]
    ext v
    simp [Module.End.mul_apply]
    have h1 : D (T v) = Tinv (D v) := by
      have h := congrArg (fun f : Module.End ℚ V => f v) hDT
      simpa [Module.End.mul_apply] using h
    have h2 : D (T (D v)) = Tinv v := by
      have h := congrArg (fun f : Module.End ℚ V => f v) hconj
      simpa [Module.End.mul_apply] using h
    rw [h1, h2]
    module
  have hrec (n : ℕ) :
      P * T ^ (n + 2) * P =
        A * (P * T ^ (n + 1) * P) +
          A * (P * T ^ (n + 1) * P) - P * T ^ n * P := by
    have hmiddle (k : ℕ) :
        (T + Tinv) * P * (P * T ^ k * P) =
          P * (T + Tinv) * T ^ k * P := by
      calc
        (T + Tinv) * P * (P * T ^ k * P) =
            (T + Tinv) * (P * P) * T ^ k * P := by
              simp only [mul_assoc]
        _ = (T + Tinv) * P * T ^ k * P := by rw [hP]
        _ = P * (T + Tinv) * T ^ k * P := by rw [hSP]
    rw [hA]
    simp only [smul_mul_assoc]
    rw [hmiddle (n + 1)]
    rw [← add_smul]
    norm_num
    simp only [mul_add, add_mul]
    have hpowT : T * T ^ (n + 1) = T ^ (n + 2) := by
      simpa [Nat.add_assoc] using (pow_succ' T (n + 1)).symm
    have hpowInv : Tinv * T ^ (n + 1) = T ^ n := by
      rw [pow_succ' T n, ← mul_assoc, hTinv, one_mul]
    have hleftT : P * T * T ^ (n + 1) * P =
        P * (T * T ^ (n + 1)) * P := by
      simp only [mul_assoc]
    have hleftInv : P * Tinv * T ^ (n + 1) * P =
        P * (Tinv * T ^ (n + 1)) * P := by
      simp only [mul_assoc]
    rw [hleftT, hleftInv, hpowT, hpowInv]
    module
  constructor
  · exact hA
  · intro n
    induction n using Nat.twoStepInduction with
    | zero =>
        simp [chebyshevFirstKind_claim10967, hP]
    | one =>
        simp [chebyshevFirstKind_claim10967, pow_one, A, mul_assoc, hP]
    | more n ih0 ih1 =>
        rw [chebyshevFirstKind_claim10967, hrec n, ih0, ih1]
        simp only [mul_assoc, add_mul, sub_mul]

end
end MathlibPlus.LinearAlgebra
