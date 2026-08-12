import Mathlib

namespace MathlibPlus.Algebra.Claim53726

noncomputable section

abbrev V (p : ℕ) := Fin 3 → ZMod p

def triangularMap {K : Type*} [CommRing K] (x : Fin 3 → K) : Fin 3 → K :=
  ![x 0, x 1 + (x 0) ^ 2, x 2 + x 0 * x 1]

def triangularMapInv {K : Type*} [CommRing K] (y : Fin 3 → K) : Fin 3 → K :=
  ![y 0, y 1 - (y 0) ^ 2, y 2 - y 0 * y 1 + (y 0) ^ 3]

theorem triangularMapInv_leftInverse {K : Type*} [CommRing K] :
    Function.LeftInverse (@triangularMapInv K _) triangularMap := by
  intro x
  funext i
  fin_cases i <;> simp [triangularMap, triangularMapInv] <;> ring

theorem triangularMapInv_rightInverse {K : Type*} [CommRing K] :
    Function.RightInverse (@triangularMapInv K _) triangularMap := by
  intro y
  funext i
  fin_cases i <;> simp [triangularMap, triangularMapInv] <;> ring

theorem triangularMap_bijective {K : Type*} [CommRing K] :
    Function.Bijective (@triangularMap K _) := by
  constructor
  · intro x y hxy
    calc
      x = triangularMapInv (triangularMap x) :=
        (triangularMapInv_leftInverse (K := K) x).symm
      _ = triangularMapInv (triangularMap y) := congrArg _ hxy
      _ = y := triangularMapInv_leftInverse (K := K) y
  · intro y
    exact ⟨triangularMapInv y, triangularMapInv_rightInverse y⟩

def q (p : ℕ) : V p ≃ V p :=
  Equiv.ofBijective (triangularMap (K := ZMod p)) (triangularMap_bijective (K := ZMod p))

def translation (p : ℕ) (v : V p) : Equiv.Perm (V p) :=
  { toFun := fun x => x + v
    invFun := fun x => x - v
    left_inv := by intro x; ext i; simp
    right_inv := by intro x; ext i; simp }

def N (p : ℕ) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure (Set.range (translation p))

def K (p : ℕ) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.map (MulAut.conj (q p)).toMonoidHom (N p)

def H (p : ℕ) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure ((N p : Set (Equiv.Perm (V p))) ∪ (K p : Set (Equiv.Perm (V p))))

def regularElementaryAbelian (p : ℕ)
    (S : Subgroup (Equiv.Perm (V p))) : Prop :=
  Function.Bijective (fun g : S => g.1 0) ∧
    Nat.card S = p ^ 3 ∧
    (∀ g : S, g ^ p = 1) ∧
    (∀ g h : S, g * h = h * g)

end

end MathlibPlus.Algebra.Claim53726

namespace MathlibPlus.Open.Algebra.Claim53726

open MathlibPlus.Algebra.Claim53726

/-- Claim 53726 with explicit translation and conjugation subgroups. -/
def triangularMapGroups : Prop :=
  ∀ p : ℕ, Nat.Prime p → 2 < p →
    Function.Bijective (triangularMap (K := ZMod p)) ∧
      regularElementaryAbelian p (N p) ∧
      regularElementaryAbelian p (K p)

end MathlibPlus.Open.Algebra.Claim53726
