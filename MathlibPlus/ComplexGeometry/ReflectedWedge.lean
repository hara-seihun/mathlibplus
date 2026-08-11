import Mathlib

/-!
# Reflected wedge root cone

Formalization of admitted claim 278.  Squared complex absolute values are represented
by `Complex.normSq`.
-/

namespace MathlibPlus.ComplexGeometry

/-- The standard alternating form on `ℂ²`. -/
def wedge (u v : ℂ × ℂ) : ℂ :=
  u.1 * v.2 - u.2 * v.1

/-- The antilinear reflection `J(v₀,v₁) = (conj v₀,-conj v₁)`. -/
def reflectedJ (v : ℂ × ℂ) : ℂ × ℂ :=
  (star v.1, -star v.2)

/-- The affine root vector `u_α=(1,α)`. -/
def rootVector (α : ℂ) : ℂ × ℂ :=
  (1, α)

/-- Direct squared wedge energy `|ω(u_α,u_β)|²`. -/
def rootDirectEnergy (α β : ℂ) : ℝ :=
  Complex.normSq (wedge (rootVector α) (rootVector β))

/-- Reflected squared wedge energy `|ω(u_α,J u_β)|²`. -/
def rootReflectedEnergy (α β : ℂ) : ℝ :=
  Complex.normSq (wedge (rootVector α) (reflectedJ (rootVector β)))

/-- The packet's scalar `K₆`, normalized so that `4K₆` is the reflected-root margin. -/
noncomputable def rootConeK6 (x y a b : ℝ) : ℝ :=
  ((a - b) ^ 2 + x ^ 2 + 6 * x * y + y ^ 2) / 4

@[simp]
theorem rootDirectEnergy_eq (α β : ℂ) :
    rootDirectEnergy α β = Complex.normSq (α - β) := by
  unfold rootDirectEnergy wedge rootVector
  simp only [one_mul, mul_one]
  rw [← Complex.normSq_neg (α - β)]
  congr 1
  ring

@[simp]
theorem rootReflectedEnergy_eq (α β : ℂ) :
    rootReflectedEnergy α β = Complex.normSq (α + star β) := by
  unfold rootReflectedEnergy wedge rootVector reflectedJ
  simp only [star_one, neg_mul, one_mul, mul_one]
  rw [← Complex.normSq_neg (α + star β)]
  congr 1
  ring

/-- For `α=x+ia` and `β=y+ib`, the reflected-root margin is `4K₆`; its nonnegativity
is equivalent to the packet's norm cone `|α-β| ≤ √2 |α+conj β|`. -/
theorem reflectedWedgeRootCone (x y a b : ℝ) :
    let α : ℂ := x + a * Complex.I
    let β : ℂ := y + b * Complex.I
    2 * rootReflectedEnergy α β - rootDirectEnergy α β =
        (a - b) ^ 2 + x ^ 2 + 6 * x * y + y ^ 2 ∧
      (a - b) ^ 2 + x ^ 2 + 6 * x * y + y ^ 2 = 4 * rootConeK6 x y a b ∧
      (rootDirectEnergy α β ≤ 2 * rootReflectedEnergy α β ↔
        ‖α - β‖ ≤ Real.sqrt 2 * ‖α + star β‖) := by
  dsimp only
  have hmargin :
      2 * rootReflectedEnergy (x + a * Complex.I) (y + b * Complex.I) -
          rootDirectEnergy (x + a * Complex.I) (y + b * Complex.I) =
        (a - b) ^ 2 + x ^ 2 + 6 * x * y + y ^ 2 := by
    simp only [rootDirectEnergy_eq, rootReflectedEnergy_eq]
    simp [Complex.normSq_apply]
    ring
  refine ⟨hmargin, ?_, ?_⟩
  · unfold rootConeK6
    ring
  · rw [rootDirectEnergy_eq, rootReflectedEnergy_eq]
    constructor
    · intro h
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.sq_norm,
        Complex.sq_norm]
      nlinarith
    · intro h
      have hsquare :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr h
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.sq_norm,
        Complex.sq_norm] at hsquare
      nlinarith

end MathlibPlus.ComplexGeometry
