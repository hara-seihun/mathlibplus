import Mathlib

/-!
# Lorentz geometry of the symmetric square of an oriented plane

The coordinate definitions and exact identities below are the four retained
claims from packet `D-0067`.
-/

namespace MathlibPlus.LorentzSymSquare

noncomputable section

abbrev Plane := Fin 2 → ℝ
abbrev SymSquare := Fin 3 → ℝ

def symplecticForm (u v : Plane) : ℝ :=
  u 0 * v 1 - u 1 * v 0

def symSquare (u v : Plane) : SymSquare :=
  ![u 0 * v 0,
    (u 0 * v 1 + u 1 * v 0) / 2,
    u 1 * v 1]

def lorentzForm (X Y : SymSquare) : ℝ :=
  X 0 * Y 2 + X 2 * Y 0 - 2 * X 1 * Y 1

def quadraticForm (X : SymSquare) : ℝ := lorentzForm X X

/-- Claim 4919: the coordinate area form is alternating. -/
theorem symplecticForm_alternating :
    (∀ u : Plane, symplecticForm u u = 0) ∧
      (∀ u v : Plane, symplecticForm v u = -symplecticForm u v) := by
  constructor <;> intros <;> simp [symplecticForm] <;> ring

/-- Claim 4920: the averaged symmetric-square coordinates commute. -/
theorem symSquare_comm (u v : Plane) : symSquare u v = symSquare v u := by
  funext i
  fin_cases i <;> simp [symSquare] <;> ring

/-- The quadratic form is the diagonal of the Lorentz bilinear form. -/
theorem quadraticForm_coordinates (X : SymSquare) :
    quadraticForm X = 2 * (X 0 * X 2 - (X 1) ^ 2) := by
  simp [quadraticForm, lorentzForm]
  ring

/-- Claim 4922: symmetry, real bilinearity, quadratic identities, and
polarization for the Lorentz form. -/
theorem lorentzForm_comm (X Y : SymSquare) :
    lorentzForm X Y = lorentzForm Y X := by
  simp [lorentzForm]
  ring

theorem lorentzForm_add_left (X Y Z : SymSquare) :
    lorentzForm (X + Y) Z = lorentzForm X Z + lorentzForm Y Z := by
  simp [lorentzForm]
  ring

theorem lorentzForm_add_right (X Y Z : SymSquare) :
    lorentzForm X (Y + Z) = lorentzForm X Y + lorentzForm X Z := by
  simp [lorentzForm]
  ring

theorem lorentzForm_smul_left (r : ℝ) (X Y : SymSquare) :
    lorentzForm (r • X) Y = r * lorentzForm X Y := by
  simp [lorentzForm]
  ring

theorem lorentzForm_smul_right (r : ℝ) (X Y : SymSquare) :
    lorentzForm X (r • Y) = r * lorentzForm X Y := by
  simp [lorentzForm]
  ring

theorem quadraticForm_add (X Y : SymSquare) :
    quadraticForm (X + Y) = quadraticForm X + 2 * lorentzForm X Y + quadraticForm Y := by
  simp [quadraticForm, lorentzForm]
  ring

theorem quadraticForm_smul (r : ℝ) (X : SymSquare) :
    quadraticForm (r • X) = r ^ 2 * quadraticForm X := by
  simp [quadraticForm, lorentzForm]
  ring

theorem lorentzForm_polarization (X Y : SymSquare) :
    lorentzForm X Y =
      (quadraticForm (X + Y) - quadraticForm X - quadraticForm Y) / 2 := by
  simp [quadraticForm, lorentzForm]
  ring

theorem lorentzForm_polarizationLaws :
    (∀ X Y : SymSquare, lorentzForm X Y = lorentzForm Y X) ∧
      (∀ X Y Z : SymSquare,
        lorentzForm (X + Y) Z = lorentzForm X Z + lorentzForm Y Z) ∧
      (∀ X Y Z : SymSquare,
        lorentzForm X (Y + Z) = lorentzForm X Y + lorentzForm X Z) ∧
      (∀ r : ℝ, ∀ X Y : SymSquare,
        lorentzForm (r • X) Y = r * lorentzForm X Y) ∧
      (∀ r : ℝ, ∀ X Y : SymSquare,
        lorentzForm X (r • Y) = r * lorentzForm X Y) ∧
      (∀ X Y : SymSquare,
        quadraticForm (X + Y) = quadraticForm X +
          2 * lorentzForm X Y + quadraticForm Y) ∧
      (∀ r : ℝ, ∀ X : SymSquare,
        quadraticForm (r • X) = r ^ 2 * quadraticForm X) ∧
      (∀ X Y : SymSquare,
        lorentzForm X Y =
          (quadraticForm (X + Y) - quadraticForm X - quadraticForm Y) / 2) := by
  exact ⟨lorentzForm_comm, lorentzForm_add_left, lorentzForm_add_right,
    lorentzForm_smul_left, lorentzForm_smul_right, quadraticForm_add,
    quadraticForm_smul, lorentzForm_polarization⟩

end

end MathlibPlus.LorentzSymSquare
