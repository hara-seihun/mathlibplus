import Mathlib

namespace MathlibPlus.Open.DihCharacterBatch

structure Dih (n : Nat) where
  i : ZMod n
  e : Bool
  deriving DecidableEq

def dmul {n : Nat} : Dih n → Dih n → Dih n
  | ⟨i, e⟩, ⟨j, f⟩ => ⟨i + (if e then -j else j), xor e f⟩

def dinv {n : Nat} : Dih n → Dih n
  | ⟨i, false⟩ => ⟨-i, false⟩
  | ⟨i, true⟩ => ⟨i, true⟩

def dpow {n : Nat} : Nat → Dih n → Dih n
  | 0, _ => ⟨0, false⟩
  | k + 1, x => dmul (dpow k x) x

lemma dmul_assoc {n : Nat} (x y z : Dih n) :
    dmul (dmul x y) z = dmul x (dmul y z) := by
  cases x with | mk i e =>
  cases y with | mk j f =>
  cases z with | mk k g =>
  cases e <;> cases f <;> cases g <;> simp [dmul]
  all_goals ring

lemma done_mul {n : Nat} (x : Dih n) : dmul ⟨0, false⟩ x = x := by
  cases x with | mk i e => cases e <;> simp [dmul]

lemma dmul_one {n : Nat} (x : Dih n) : dmul x ⟨0, false⟩ = x := by
  cases x with | mk i e => cases e <;> simp [dmul]

lemma dinv_mul {n : Nat} (x : Dih n) : dmul (dinv x) x = ⟨0, false⟩ := by
  cases x with | mk i e =>
  cases e <;> simp [dmul, dinv]

instance {n : Nat} : Group (Dih n) where
  mul := dmul
  one := ⟨0, false⟩
  inv := dinv
  npow := dpow
  mul_assoc := dmul_assoc
  one_mul := done_mul
  mul_one := dmul_one
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl
  inv_mul_cancel := dinv_mul

def rotation {n : Nat} : Dih n := ⟨1, false⟩
def reflection {n : Nat} : Dih n := ⟨0, true⟩

/-- Claim 25557: the sign assignment on the dihedral generators is a
one-dimensional character whenever the rotation order is even. -/
def claim25557 : Prop :=
  ∀ {n : Nat}, n % 2 = 0 →
    ∃ χ : Dih n →* Units ℤ,
      χ rotation = (-1 : Units ℤ) ∧
      χ reflection = (-1 : Units ℤ)

end MathlibPlus.Open.DihCharacterBatch
