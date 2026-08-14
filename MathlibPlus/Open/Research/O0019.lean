import Mathlib

namespace MathlibPlus.Open.Research.O0019

open scoped BigOperators

abbrev Torus (N : ℕ) := ZMod N × ZMod N

/-- A direction whose two coordinates generate the unit ideal modulo `N`. -/
def primitiveDirection (N : ℕ) (v : Torus N) : Prop :=
  ∃ a b : ZMod N, a * v.1 + b * v.2 = 1

abbrev PrimitiveDirection (N : ℕ) := {v : Torus N // primitiveDirection N v}

def linePoint {N : ℕ} (v b : Torus N) (t : ZMod N) : Torus N :=
  (b.1 + t * v.1, b.2 + t * v.2)

/-- The full affine-line Radon transform, indexed by every primitive direction
and every affine base point. -/
def fullPrimitiveLineRadonTransform (N : ℕ) (hN : 2 ≤ N)
    {R : Type*} [AddCommMonoid R] (signal : Torus N → R) :
    PrimitiveDirection N → Torus N → R := by
  letI : NeZero N := ⟨by omega⟩
  exact fun v b => ∑ t : ZMod N, signal (linePoint v.1 b t)

/-- Every frequency is a scalar multiple of a primitive direction. -/
def claim9596 : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ r s : ZMod N,
    ∃ v : Torus N, primitiveDirection N v ∧
      ∃ t : ZMod N, (r, s) = linePoint v (0, 0) t

/-- The full primitive-line transform is injective on complex-valued signals. -/
def claim9598 : Prop :=
  ∀ (N : ℕ) (hN : 2 ≤ N) (f g : Torus N → ℂ),
    fullPrimitiveLineRadonTransform N hN f =
        fullPrimitiveLineRadonTransform N hN g → f = g

/-- Coordinatewise row weighting makes a zero-weight observation vanish for
all signals, without forcing the corresponding signal coordinate to vanish. -/
def weightedObservation (n : ℕ) (w x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w i * x i

def claim9603 : Prop :=
  ∀ (n : ℕ) (w : Fin n → ℝ) (i : Fin n), w i = 0 →
    (∀ x : Fin n → ℝ, weightedObservation n w x i = 0) ∧
      ∃ x : Fin n → ℝ, x i ≠ 0

end MathlibPlus.Open.Research.O0019
