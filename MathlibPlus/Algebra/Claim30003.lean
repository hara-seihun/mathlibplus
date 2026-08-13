import Mathlib

namespace MathlibPlus.Algebra.Claim30003

variable {A : Type*} [CommRing A]

/-- The adjoint (circle) operation on a commutative ring with zero triple products. -/
def circleMul (x y : A) : A := x + y + x * y

/-- The quadratic change of coordinates from addition to the adjoint operation. -/
def q (c x : A) : A := x + c * x ^ 2

/-- The inverse quadratic change of coordinates. -/
def qInv (c x : A) : A := x - c * x ^ 2

lemma sq_mul_zero (hnil : ∀ x y z : A, x * y * z = 0) (x y : A) :
    x ^ 2 * y = 0 := by
  simpa [pow_two, mul_assoc] using hnil x x y

lemma mul_sq_zero (hnil : ∀ x y z : A, x * y * z = 0) (x y : A) :
    x * y ^ 2 = 0 := by
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnil x y y

lemma sq_sq_zero (hnil : ∀ x y z : A, x * y * z = 0) (x y : A) :
    x ^ 2 * y ^ 2 = 0 := by
  calc
    x ^ 2 * y ^ 2 = (x * x * y) * y := by ring
    _ = 0 := by rw [hnil x x y]; simp

lemma q_mul_q (c : A) (hnil : ∀ x y z : A, x * y * z = 0) (x y : A) :
    q c x * q c y = x * y := by
  have hxy : x ^ 2 * y = 0 := sq_mul_zero hnil x y
  have hyx : x * y ^ 2 = 0 := mul_sq_zero hnil x y
  have hxxyy : x ^ 2 * y ^ 2 = 0 := sq_sq_zero hnil x y
  dsimp [q]
  calc
    (x + c * x ^ 2) * (y + c * y ^ 2) =
        x * y + c * (x ^ 2 * y) + c * (x * y ^ 2) + c ^ 2 * (x ^ 2 * y ^ 2) := by ring
    _ = x * y := by rw [hxy, hyx, hxxyy]; ring

lemma q_square (c : A) (hnil : ∀ x y z : A, x * y * z = 0) (x : A) :
    q c x ^ 2 = x ^ 2 := by
  have hxxx : x ^ 3 = 0 := by
    simpa [pow_succ, mul_assoc] using hnil x x x
  have hxxxx : x ^ 4 = 0 := by
    calc
      x ^ 4 = x ^ 3 * x := by ring
      _ = 0 := by rw [hxxx]; simp
  dsimp [q]
  calc
    (x + c * x ^ 2) ^ 2 = x ^ 2 + 2 * c * x ^ 3 + c ^ 2 * x ^ 4 := by ring
    _ = x ^ 2 := by rw [hxxx, hxxxx]; ring

lemma qInv_square (c : A) (hnil : ∀ x y z : A, x * y * z = 0) (x : A) :
    qInv c x ^ 2 = x ^ 2 := by
  have hxxx : x ^ 3 = 0 := by
    simpa [pow_succ, mul_assoc] using hnil x x x
  have hxxxx : x ^ 4 = 0 := by
    calc
      x ^ 4 = x ^ 3 * x := by ring
      _ = 0 := by rw [hxxx]; simp
  dsimp [qInv]
  calc
    (x - c * x ^ 2) ^ 2 = x ^ 2 - 2 * c * x ^ 3 + c ^ 2 * x ^ 4 := by ring
    _ = x ^ 2 := by rw [hxxx, hxxxx]; ring

theorem q_circle (c : A) (hc : (2 : A) * c = 1)
    (hnil : ∀ x y z : A, x * y * z = 0) (x y : A) :
    circleMul (q c x) (q c y) = q c (x + y) := by
  have hprod := q_mul_q c hnil x y
  dsimp [circleMul]
  rw [hprod]
  dsimp [q]
  calc
    x + c * x ^ 2 + (y + c * y ^ 2) + x * y =
        x + y + c * x ^ 2 + c * y ^ 2 + x * y := by ring
    _ = x + y + c * (x + y) ^ 2 := by
      have hcross : x * y * c * 2 = x * y := by
        calc
          x * y * c * 2 = (2 * c) * (x * y) := by ring
          _ = x * y := by rw [hc]; ring
      ring_nf
      rw [hcross]

theorem qInv_q (c : A) (hnil : ∀ x y z : A, x * y * z = 0) (x : A) :
    qInv c (q c x) = x := by
  have hsq := q_square c hnil x
  dsimp [qInv]
  rw [hsq]
  dsimp [q]
  ring

theorem q_qInv (c : A) (hnil : ∀ x y z : A, x * y * z = 0) (x : A) :
    q c (qInv c x) = x := by
  have hsq := qInv_square c hnil x
  dsimp [q]
  rw [hsq]
  dsimp [qInv]
  ring

/-- The two-sided inverse equivalence supplied by the quadratic formula. -/
def qEquiv (c : A) (hnil : ∀ x y z : A, x * y * z = 0) : A ≃ A where
  toFun := q c
  invFun := qInv c
  left_inv := qInv_q c hnil
  right_inv := q_qInv c hnil

lemma algebra_two_inv_two {p : ℕ} (hp2 : 2 < p) (hp : p.Prime)
    (A : Type*) [CommRing A] [Algebra (ZMod p) A] :
    (2 : A) * algebraMap (ZMod p) A ((2 : ZMod p)⁻¹) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    simp [ZMod.val_ofNat, Nat.mod_eq_of_lt hp2] at hv
  have hmap : (2 : A) = algebraMap (ZMod p) A (2 : ZMod p) := by
    simpa using (map_natCast (algebraMap (ZMod p) A) 2).symm
  rw [hmap, ← map_mul]
  rw [mul_inv_cancel₀ h2]
  simp

/-- The all-prime two-step radical quadratic change of coordinates. -/
def quadraticAdditiveCircleIsomorphism_claim30003 : Prop :=
  ∀ (p : ℕ), 2 < p → (hp : p.Prime) →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (A : Type*) [CommRing A] [Algebra (ZMod p) A]
      [FiniteDimensional (ZMod p) A],
      (∀ x y z : A, x * y * z = 0) →
      let c : A := algebraMap (ZMod p) A ((2 : ZMod p)⁻¹)
      (∀ x y, circleMul (q c x) (q c y) = q c (x + y)) ∧
        (∀ x, qInv c (q c x) = x) ∧ (∀ x, q c (qInv c x) = x)

theorem quadraticAdditiveCircleIsomorphism_claim30003_proved :
    quadraticAdditiveCircleIsomorphism_claim30003 := by
  intro p hp2 hp
  letI : Fact p.Prime := ⟨hp⟩
  intro A instCommRing instAlgebra instFiniteDimensional hnil
  let c : A := algebraMap (ZMod p) A ((2 : ZMod p)⁻¹)
  have hc : (2 : A) * c = 1 := by
    dsimp [c]
    exact algebra_two_inv_two hp2 hp A
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact q_circle c hc hnil x y
  · intro x
    exact qInv_q c hnil x
  · intro x
    exact q_qInv c hnil x

end MathlibPlus.Algebra.Claim30003
