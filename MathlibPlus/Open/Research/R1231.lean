import Mathlib

namespace MathlibPlus.Open.Research.R1231

abbrev F3 := ZMod 3
abbrev F3Vec (n : Nat) := Fin n → F3

noncomputable section

def Q (x : F3Vec 2) : F3Vec 3 :=
  ![x 0 * (x 0 - 1), (2 : F3) * x 0 * x 1 - x 1, x 1 ^ 2]

def displacement (s x : F3Vec 2) : F3Vec 3 :=
  Q (x + s) - Q x - Q s

def displacementPlane (x : F3Vec 2) : Set (F3Vec 3) :=
  Set.range (fun s : F3Vec 2 => displacement s x)

def IsTwoDimensionalPlane (S : Set (F3Vec 3)) : Prop :=
  ∃ W : Submodule F3 (F3Vec 3),
    (W : Set (F3Vec 3)) = S ∧ Module.finrank F3 W = 2

def claim30390 : Prop :=
  ∀ x : F3Vec 2, x ≠ 0 →
    IsTwoDimensionalPlane (displacementPlane x) ∧ Q x ∈ displacementPlane x

def dot (u v : F3Vec 3) : F3 :=
  ∑ i, u i * v i

def annihilator (S : Set (F3Vec 3)) : Set (F3Vec 3) :=
  {c | ∀ y, y ∈ S → dot c y = 0}

def line (c : F3Vec 3) : Set (F3Vec 3) :=
  {d | ∃ a : F3, d = a • c}

def ell (x : F3Vec 2) : F3Vec 3 :=
  ![x 1 ^ 2, -(x 0 * x 1), x 0 ^ 2]

def polar (m : F3Vec 3 → F3) (u v : F3Vec 3) : F3 :=
  m (u + v) - m u - m v

def polarRadical (m : F3Vec 3 → F3) : Set (F3Vec 3) :=
  {u | ∀ v, polar m u v = 0}

def IsHomogeneousQuadratic (m : F3Vec 3 → F3) : Prop :=
  ∃ B : (F3Vec 3) →ₗ[F3] (F3Vec 3) →ₗ[F3] F3,
    (∀ u v, B u v = B v u) ∧ ∀ u, m u = B u u

def IsNonzeroHomogeneousQuadratic (m : F3Vec 3 → F3) : Prop :=
  IsHomogeneousQuadratic m ∧ ∃ u, m u ≠ 0

def ProjectivelyEquivalent (m n : F3Vec 3 → F3) : Prop :=
  ∃ c : F3, c ≠ 0 ∧ ∀ u, m u = c * n u

def ProjectivelyEquivalentVector (x y : F3Vec 2) : Prop :=
  ∃ c : F3, c ≠ 0 ∧ x = c • y

def projectiveDirections : Finset (F3Vec 2) :=
  {![1, 0], ![1, 1], ![1, 2], ![0, 1]}

def IsRankOneHomogeneousQuadratic (m : F3Vec 3 → F3) : Prop :=
  ∃ l : F3Vec 3, l ≠ 0 ∧
    ProjectivelyEquivalent m (fun u => dot l u ^ 2)

def alignedSquare (m : F3Vec 3 → F3) (x : F3Vec 2) : Prop :=
  ProjectivelyEquivalent m (fun u => dot (ell x) u ^ 2)

def claim30391 : Prop :=
  (∀ x : F3Vec 2, x ≠ 0 → annihilator (displacementPlane x) = line (ell x)) ∧
    projectiveDirections.card = 4 ∧
    (∀ x : F3Vec 2, x ≠ 0 →
      ∃ y, y ∈ projectiveDirections ∧ ProjectivelyEquivalentVector x y) ∧
    (∀ m : F3Vec 3 → F3, IsNonzeroHomogeneousQuadratic m →
      ((∃ x : F3Vec 2, x ≠ 0 ∧
          ∀ y, y ∈ displacementPlane x → y ∈ polarRadical m) ↔
        ∃ x : F3Vec 2, x ∈ projectiveDirections ∧
          IsRankOneHomogeneousQuadratic m ∧ alignedSquare m x))

end

end MathlibPlus.Open.Research.R1231
