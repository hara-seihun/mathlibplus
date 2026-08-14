import Mathlib

open scoped LinearAlgebra.Projectivization

namespace MathlibPlus.Open.AlgebraicGeometry.FermatQuinticBatch

noncomputable section

private abbrev V := Fin 4 → ℂ
private abbrev P := ℙ ℂ V
private def fermatPoint (p : P) : Prop :=
  ∑ i : Fin 4, (p.rep i) ^ 5 = 0

private def primitiveFifthRoot (ζ : ℂ) : Prop :=
  ζ ^ 5 = 1 ∧ ζ ≠ 1 ∧ ζ ≠ 0

private def diagonalMap (ζ : ℂ) : V →ₗ[ℂ] V :=
  { toFun := fun x i ↦ ζ ^ (i : ℕ) * x i
    map_add' := by
      intro x y
      funext i
      simp only [Pi.add_apply]
      ring
    map_smul' := by
      intro c x
      funext i
      simp only [Pi.smul_apply, RingHom.id_apply]
      ring }

private def diagonalInjective (ζ : ℂ) (hζ : ζ ≠ 0) :
    Function.Injective (diagonalMap ζ) := by
  intro x y h
  funext i
  have hi : ζ ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hζ
  exact mul_left_cancel₀ hi (congrFun h i)

private def gPoint (ζ : ℂ) (hζ : ζ ≠ 0) : P → P :=
  Projectivization.map (diagonalMap ζ) (diagonalInjective ζ hζ)

private def atMostOneNonzero (x : V) : Prop :=
  ∀ i j : Fin 4, x i ≠ 0 → x j ≠ 0 → i = j

private def actionOnFermat (ζ : ℂ) (hζ : ζ ≠ 0)
    (hpres : ∀ p : P, fermatPoint p → fermatPoint (gPoint ζ hζ p)) :
    {p : P // fermatPoint p} → {p : P // fermatPoint p} :=
  fun p ↦ ⟨gPoint ζ hζ p.1, hpres p.1 p.2⟩

/-- Claim 46202: the diagonal fifth-root map preserves the Fermat quintic and
its powers supply a faithful `C₅` action. -/
def claim46202 : Prop :=
  ∀ ζ : ℂ, primitiveFifthRoot ζ → ∀ hζ : ζ ≠ 0,
    (∀ p : P, fermatPoint p → fermatPoint (gPoint ζ hζ p)) ∧
      ∃ act : ZMod 5 → {p : P // fermatPoint p} → {p : P // fermatPoint p},
        (∀ p, act 0 p = p) ∧
          (∀ a b p, act (a + b) p = act a (act b p)) ∧
          (∀ p, (act 1 p).1 = gPoint ζ hζ p.1) ∧
          (∀ a b, (∀ p, act a p = act b p) → a = b)

/-- Claim 46207: a nonidentity power has no projective fixed point; the
coordinate-eigenvalue argument is retained as an explicit conjunct. -/
def claim46207 : Prop :=
  ∀ ζ : ℂ, primitiveFifthRoot ζ → ∀ hζ : ζ ≠ 0,
    ∀ hpres : (∀ p : P, fermatPoint p → fermatPoint (gPoint ζ hζ p)),
    ∀ (k : Fin 5) (p : {p : P // fermatPoint p}), k ≠ 0 →
      (actionOnFermat ζ hζ hpres)^[k.val] p ≠ p ∧
        ((actionOnFermat ζ hζ hpres)^[k.val] p = p →
          ∃ c : ℂ,
            c ≠ 0 ∧
              (∀ i : Fin 4,
                ζ ^ (k.val * (i : ℕ)) * p.1.rep i = c * p.1.rep i) ∧
              atMostOneNonzero p.1.rep ∧
              (∃ i : Fin 4, ∀ j : Fin 4, p.1.rep j ≠ 0 → j = i) ∧
              ¬ fermatPoint p.1)

end
end MathlibPlus.Open.AlgebraicGeometry.FermatQuinticBatch
