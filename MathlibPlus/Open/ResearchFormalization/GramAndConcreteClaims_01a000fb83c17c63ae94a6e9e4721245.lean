import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

noncomputable def cayleyAdjacency {G : Type*} [Fintype G] [Group G]
    (S : Set G) : Matrix G G ℝ := by
  classical
  exact fun x y => if x⁻¹ * y ∈ S then 1 else 0

noncomputable def shiftedAdjacency {G : Type*} [Fintype G] [Group G]
    (S : Set G) (lambda : ℝ) : Matrix G G ℝ := by
  classical
  exact fun x y => cayleyAdjacency S x y + if x = y then lambda else 0

noncomputable def shiftedGram {G : Type*} [Fintype G] [Group G]
    (S : Set G) (lambda : ℝ) : Matrix G G ℝ :=
  Matrix.transpose (shiftedAdjacency S lambda) * shiftedAdjacency S lambda

def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ g, g ∈ S ↔ g⁻¹ ∈ S

def identityFree {G : Type*} [Group G] (S : Set G) : Prop :=
  (1 : G) ∉ S

def positiveSemidefinite {G : Type*} [Fintype G]
    (M : Matrix G G ℝ) : Prop := Matrix.PosSemidef M

noncomputable def gramProfile {G : Type*} [Fintype G] [Group G]
    (S : Set G) (lambda : ℝ) (g : G) : ℝ :=
  shiftedGram S lambda 1 g

noncomputable def gramSeparated {G : Type*} [Fintype G] [Group G]
    (S : Set G) (lambda : ℝ) : Prop :=
  ∀ g h, gramProfile S lambda g = gramProfile S lambda h ↔
    h = g ∨ h = g⁻¹

def inversePairSymmetric {G : Type*} [Fintype G] [Group G]
    (S : Set G) (lambda : ℝ) : Prop :=
  ∀ g, gramProfile S lambda g = gramProfile S lambda g⁻¹

def shiftedAdjacencyGramStatement : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G] (S : Set G) (lambda : ℝ),
    inverseClosed S → identityFree S →
      positiveSemidefinite (shiftedGram S lambda) ∧
      inversePairSymmetric S lambda

abbrev Q12 := ZMod 6 × ZMod 2
abbrev C7Q12 := ZMod 7 × Q12

def q12Mul (a b : Q12) : Q12 :=
  (a.1 + (if a.2 = 0 then b.1 else -b.1) +
      (3 : ZMod 6) * (a.2.val : ZMod 6) * (b.2.val : ZMod 6),
    a.2 + b.2)

def q12Inv (a : Q12) : Q12 :=
  if a.2 = 0 then (-a.1, 0) else (a.1 + 3, 1)

def q12Zero : Q12 := (0, 0)
def q12Z : Q12 := (3, 0)

def c7q12Mul (a b : C7Q12) : C7Q12 :=
  (a.1 + b.1, q12Mul a.2 b.2)

def c7q12Inv (a : C7Q12) : C7Q12 :=
  (-a.1, q12Inv a.2)

def c7q12One : C7Q12 := (0, q12Zero)

def q12T0 (a : Q12) : Prop :=
  a.2 = 0 ∧ (a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 4 ∨ a.1 = 5)

def c7q12S (a : C7Q12) : Prop :=
  a.1 ≠ 0 ∨ (a.1 = 0 ∧ q12T0 a.2)

def c7q12Adj (x y : C7Q12) : Prop :=
  c7q12S (c7q12Mul (c7q12Inv x) y)

def c7q12Undirected : Prop :=
  ∀ x y, c7q12Adj x y ↔ c7q12Adj y x

noncomputable def c7q12ShiftedAdjacency : Matrix C7Q12 C7Q12 ℝ := by
  classical
  exact fun x y =>
    (if c7q12Adj x y then 1 else 0) +
      (if x = y then 84 else 0)

noncomputable def c7q12Gram : Matrix C7Q12 C7Q12 ℝ :=
  Matrix.transpose c7q12ShiftedAdjacency * c7q12ShiftedAdjacency

noncomputable def c7q12Valency : Prop := by
  classical
  exact ∀ x, (Finset.univ.filter (fun y => c7q12Adj x y)).card = 76

def c7q12InverseClosed : Prop :=
  ∀ a, c7q12S a ↔ c7q12S (c7q12Inv a)

def c7q12IdentityFree : Prop := ¬c7q12S c7q12One

def c7q12Connected : Prop :=
  ∀ x y, Relation.ReflTransGen c7q12Adj x y

def c7q12GramCollision : Prop :=
  c7q12IdentityFree ∧
  c7q12InverseClosed ∧
  c7q12Undirected ∧
  c7q12Connected ∧
  c7q12Valency ∧
  Fintype.card C7Q12 = 84 ∧
  (∀ a, a.1 ≠ 0 → c7q12Gram c7q12One a = 236) ∧
  c7q12Gram c7q12One (1, q12Zero) =
    c7q12Gram c7q12One (1, q12Z) ∧
  c7q12Inv (1, q12Zero) ≠ (1, q12Z)

def cayleyAutomorphism {G : Type*} [Group G]
    (S : Set G) (f : Equiv.Perm G) : Prop :=
  ∀ x y, x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ S

def inversePairSchemeStatement : Prop :=
  ∀ (G : Type*) [Fintype G] [Group G] (S : Set G) (lambda : ℝ),
    identityFree S → inverseClosed S → gramSeparated S lambda →
      (∀ f : Equiv.Perm G, cayleyAutomorphism S f → ∀ x y,
        shiftedGram S lambda (f x) (f y) = shiftedGram S lambda x y) ∧
      (∀ f : Equiv.Perm G, cayleyAutomorphism S f → f 1 = 1 →
        ∀ g, f g = g ∨ f g = g⁻¹) ∧
      (∀ f : Equiv.Perm G, cayleyAutomorphism S f → ∀ x y,
        (f x)⁻¹ * f y = x⁻¹ * y ∨
          (f x)⁻¹ * f y = (x⁻¹ * y)⁻¹)

end ResearchFormalization
end Open
end MathlibPlus
