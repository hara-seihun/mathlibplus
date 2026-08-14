import Mathlib

namespace MathlibPlus.Open.Research.TernaryHenon

/-! Mixed-difference spans for the three explicit maps over F₃. -/

abbrev F3 := ZMod 3
abbrev Vec3 := Fin 3 → F3

def vec3 (a b c : F3) : Vec3 := ![a, b, c]

def henonF1 (z : Vec3) : Vec3 :=
  vec3 (z 0 ^ 2 + z 0 * z 1 * z 2) (z 1 ^ 2) (z 2 ^ 2)

def henonF2 (z : Vec3) : Vec3 :=
  vec3 (z 0 ^ 2 * z 1) (z 1 ^ 2) (z 2 ^ 2)

def henonF3 (z : Vec3) : Vec3 :=
  vec3 (z 0 ^ 2 * z 1) (z 1 ^ 2 * z 2) (z 2 ^ 2 * z 0)

def mixedDifference (f : Vec3 → Vec3) (y z : Vec3) : Vec3 :=
  f (y + z) - f y - f z

def mixedDifferenceSpan (f : Vec3 → Vec3) (z : Vec3) : Submodule F3 Vec3 :=
  Submodule.span F3 (Set.range (fun y : Vec3 => mixedDifference f y z))

def e₁ : Vec3 := vec3 1 0 0
def e₂ : Vec3 := vec3 0 1 0
def e₃ : Vec3 := vec3 0 0 1

def spanE₁ : Submodule F3 Vec3 := Submodule.span F3 {e₁}
def spanE₁E₂ : Submodule F3 Vec3 := Submodule.span F3 {e₁, e₂}
def spanE₁E₃ : Submodule F3 Vec3 := Submodule.span F3 {e₁, e₃}

/-- Faithful open statement for Claim 56730. -/
def claim56730 : Prop :=
  ∀ z : Vec3,
    (z = 0 → mixedDifferenceSpan henonF1 z = ⊥) ∧
    ((z 1 = 0 ∧ z 2 = 0 ∧ z 0 ≠ 0) →
      mixedDifferenceSpan henonF1 z = spanE₁) ∧
    ((z 1 ≠ 0 ∧ z 2 = 0) →
      mixedDifferenceSpan henonF1 z = spanE₁E₂) ∧
    ((z 1 = 0 ∧ z 2 ≠ 0) →
      mixedDifferenceSpan henonF1 z = spanE₁E₃) ∧
    ((z 1 * z 2 ≠ 0) → mixedDifferenceSpan henonF1 z = ⊤) ∧
    henonF1 z ∈ mixedDifferenceSpan henonF1 z

/-- Faithful open statement for Claim 56731. -/
def claim56731 : Prop :=
  ∀ z : Vec3,
    henonF2 z ∈ mixedDifferenceSpan henonF2 z ∧
    henonF3 z ∈ mixedDifferenceSpan henonF3 z

end MathlibPlus.Open.Research.TernaryHenon
