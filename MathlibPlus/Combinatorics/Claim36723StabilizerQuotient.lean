import Mathlib

namespace MathlibPlus.Combinatorics.Claim36723

noncomputable section
open scoped BigOperators
open Classical

abbrev BooleanCube36723 (n : ℕ) := Fin n → ZMod 2

/-- The direction-`i` base fiber of the Boolean cube. -/
def directionSpace36723 (n : ℕ) (i : Fin n) :
    Submodule (ZMod 2) (BooleanCube36723 n) :=
  { carrier := {x | x i = 0}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy
      change x i = 0 at hx
      change y i = 0 at hy
      change (x + y) i = 0
      simp [hx, hy]
    smul_mem' := by
      intro c x hx
      change x i = 0 at hx
      change (c • x) i = 0
      simp [hx] }

abbrev DirectionFiber36723 (n : ℕ) (i : Fin n) := directionSpace36723 n i

noncomputable instance directionFiberFintype36723 (n : ℕ) (i : Fin n) :
    Fintype (DirectionFiber36723 n i) := Fintype.ofFinite _

/-- The literal translation orbit of a Boolean-valued function. -/
def translationOrbit36723 {V : Type*} [Fintype V] [Add V]
    (f : V → Bool) : Finset (V → Bool) :=
  Finset.univ.image (fun a x => f (x + a))

def translationOrbitCard36723 {V : Type*} [Fintype V] [Add V]
    (f : V → Bool) : ℕ :=
  (translationOrbit36723 f).card

lemma zmod2_cases36723 (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have hc : c.val < 2 := ZMod.val_lt c
  have h : c.val = 0 ∨ c.val = 1 := by omega
  rcases h with h | h
  · left
    rw [← ZMod.natCast_zmod_val c, h]
    rfl
  · right
    rw [← ZMod.natCast_zmod_val c, h]
    rfl

/-- The translation stabilizer, as a subspace of the exact direction fiber. -/
def translationStabilizer36723 {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (f : V → Bool) : Submodule (ZMod 2) V :=
  { carrier := {a | ∀ x, f (x + a) = f x}
    zero_mem' := by
      intro x
      simp
    add_mem' := by
      intro a b ha hb x
      calc
        f (x + (a + b)) = f ((x + b) + a) := by
          congr 1
          abel
        _ = f (x + b) := ha (x + b)
        _ = f x := hb x
    smul_mem' := by
      intro c a ha x
      rcases zmod2_cases36723 c with rfl | rfl
      · simp
      · simpa using ha x }

/-- The quotient map `F_i : Ω_i → W_i`. -/
def quotientMap36723 {n : ℕ} {i : Fin n}
    (f : DirectionFiber36723 n i → Bool) :
    DirectionFiber36723 n i →ₗ[ZMod 2]
      (DirectionFiber36723 n i ⧸ translationStabilizer36723 f) :=
  Submodule.mkQ (translationStabilizer36723 f)

/-- Claim 36723: the translation stabilizer quotient is a lossless quotient
vector-space carrier of size at most the fixed orbit bound. -/
def exactStabilizerQuotientFactorization_claim36723 : Prop :=
  ∀ (n : ℕ) (i : Fin n) (M : ℕ)
    (f : DirectionFiber36723 n i → Bool),
    translationOrbitCard36723 f ≤ M →
    ∃ S : Set (DirectionFiber36723 n i ⧸ translationStabilizer36723 f),
      (∀ x : DirectionFiber36723 n i,
        f x = true ↔ quotientMap36723 f x ∈ S) ∧
      Nat.card (DirectionFiber36723 n i ⧸ translationStabilizer36723 f) ≤ M

end

end MathlibPlus.Combinatorics.Claim36723
