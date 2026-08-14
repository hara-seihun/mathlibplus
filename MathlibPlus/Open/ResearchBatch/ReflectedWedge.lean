import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchBatch.ReflectedWedge

def wedge (u v : ℂ × ℂ) : ℂ := u.1 * v.2 - u.2 * v.1

def reflected (u : ℂ × ℂ) : ℂ × ℂ := (star u.1, -star u.2)

def rootVector (α : ℂ) : ℂ × ℂ := (1, α)

def reflected_wedge_root_energies : Prop :=
  ∀ α β : ℂ,
    Complex.normSq (wedge (rootVector α) (rootVector β)) =
        Complex.normSq (α - β) ∧
    Complex.normSq (wedge (rootVector α) (reflected (rootVector β))) =
        Complex.normSq (α + star β)

def per_weight_cone_margin : Prop :=
  ∀ U Φ : ℝ,
    2 * (Real.exp U + Real.exp (-U) + 2 * Real.cos Φ) -
        (Real.exp U + Real.exp (-U) - 2 * Real.cos Φ) =
      Real.exp U + Real.exp (-U) + 6 * Real.cos Φ

def matrixApply (A : Matrix (Fin 2) (Fin 2) ℂ) (u : ℂ × ℂ) : ℂ × ℂ :=
  (A 0 0 * u.1 + A 0 1 * u.2,
    A 1 0 * u.1 + A 1 1 * u.2)

def matrixDet (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

def reflection_commutes (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ u : ℂ × ℂ, matrixApply A (reflected u) = reflected (matrixApply A u)

def reflection_equivariant_congruence_preserves_cone_sign : Prop :=
  ∀ (A : Matrix (Fin 2) (Fin 2) ℂ), matrixDet A ≠ 0 → reflection_commutes A →
    ∀ u v : ℂ × ℂ,
      Complex.normSq (wedge (matrixApply A u) (matrixApply A v)) =
          Complex.normSq (matrixDet A) * Complex.normSq (wedge u v) ∧
      Complex.normSq
          (wedge (matrixApply A u) (reflected (matrixApply A v))) =
          Complex.normSq (matrixDet A) *
            Complex.normSq (wedge u (reflected v)) ∧
      (2 * Complex.normSq (wedge u (reflected v)) -
            Complex.normSq (wedge u v) < 0 →
        2 * Complex.normSq
              (wedge (matrixApply A u) (reflected (matrixApply A v))) -
            Complex.normSq (wedge (matrixApply A u) (matrixApply A v)) < 0)

end MathlibPlus.Open.ResearchBatch.ReflectedWedge
