import Mathlib

namespace MathlibPlus.Open.Combinatorics.BatchSemidirectOrbits

abbrev F7 := ZMod 7
abbrev V := F7 × F7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
abbrev C3 := Multiplicative (ZMod 3)
abbrev VN := Multiplicative V

def scalar (i : ZMod 3) : F7 := (2 : F7) ^ i.val

def scale (i : ZMod 3) : V ≃+ V :=
  { toFun := fun v => (scalar i * v.1, scalar i * v.2)
    invFun := fun v => ((scalar i)⁻¹ * v.1, (scalar i)⁻¹ * v.2)
    left_inv := by
      intro v
      have hi : scalar i ≠ 0 := by
        dsimp [scalar]
        exact pow_ne_zero _ (by decide)
      ext
      · change (scalar i)⁻¹ * (scalar i * v.1) = v.1
        rw [← mul_assoc, inv_mul_cancel₀ hi, one_mul]
      · change (scalar i)⁻¹ * (scalar i * v.2) = v.2
        rw [← mul_assoc, inv_mul_cancel₀ hi, one_mul]
    right_inv := by
      intro v
      have hi : scalar i ≠ 0 := by
        dsimp [scalar]
        exact pow_ne_zero _ (by decide)
      ext
      · change scalar i * ((scalar i)⁻¹ * v.1) = v.1
        rw [← mul_assoc, mul_inv_cancel₀ hi, one_mul]
      · change scalar i * ((scalar i)⁻¹ * v.2) = v.2
        rw [← mul_assoc, mul_inv_cancel₀ hi, one_mul]
    map_add' := by
      intro v w
      ext <;> simp [mul_add] }

lemma scalar_zero : scalar (0 : ZMod 3) = 1 := by
  native_decide

lemma scalar_add (i j : ZMod 3) : scalar (i + j) = scalar i * scalar j := by
  fin_cases i <;> fin_cases j <;> native_decide

def action (i : C3) : MulAut VN :=
  AddEquiv.toMultiplicative (scale i)

def actionHom : C3 →* MulAut VN :=
  { toFun := action
    map_one' := by
      apply MulEquiv.ext
      intro v
      change (scalar 0 * v.1, scalar 0 * v.2) = v
      rw [scalar_zero]
      cases v
      simp
    map_mul' := by
      intro i j
      apply MulEquiv.ext
      intro v
      change (scalar (Multiplicative.toAdd i + Multiplicative.toAdd j) * v.1,
          scalar (Multiplicative.toAdd i + Multiplicative.toAdd j) * v.2) =
        (scalar (Multiplicative.toAdd i) * (scalar (Multiplicative.toAdd j) * v.1),
          scalar (Multiplicative.toAdd i) * (scalar (Multiplicative.toAdd j) * v.2))
      rw [scalar_add]
      congr 1 <;> ring }

abbrev SD := VN ⋊[actionHom] C3

structure G where
  index : C3
  vector : V
deriving DecidableEq, Fintype

def carrierEquiv : G ≃ SD :=
  { toFun := fun p => SemidirectProduct.mk (Multiplicative.ofAdd p.vector) p.index
    invFun := fun g => ⟨g.right, Multiplicative.toAdd g.left⟩
    left_inv := by
      intro p
      cases p
      rfl
    right_inv := by
      intro g
      cases g
      rfl }

instance : Group G := carrierEquiv.group

def c3Zero : C3 := Multiplicative.ofAdd 0

def multiplicationFormula (a b : G) : G :=
  ⟨Multiplicative.ofAdd (Multiplicative.toAdd a.index + Multiplicative.toAdd b.index),
    (a.vector.1 + scalar (Multiplicative.toAdd a.index) * b.vector.1,
      a.vector.2 + scalar (Multiplicative.toAdd a.index) * b.vector.2)⟩

def N : Finset G := by
  classical
  exact Finset.univ.filter (fun g => g.index = c3Zero)

def inverseClosed (S : Finset G) : Prop :=
  S ⊆ N ∧ 1 ∉ S ∧ ∀ g ∈ S, g⁻¹ ∈ S

def X := {S : Finset G // inverseClosed S}

noncomputable instance : Fintype X := by
  classical
  exact Fintype.subtype (Finset.univ.filter inverseClosed) (by
    intro S
    simp)

def autImage (φ : MulAut G) (S : Finset G) : Finset G := S.image φ

noncomputable def orbit (S : X) : Finset X := by
  classical
  exact Finset.univ.filter (fun T => ∃ φ : MulAut G, T.1 = autImage φ S.1)

noncomputable def orbits : Finset (Finset X) := by
  classical
  exact Finset.univ.image orbit

noncomputable def orbitCount (k : ℕ) : ℕ := (orbits.filter (fun O => O.card = k)).card

def finite_semidirect_orbit_histogram : Prop :=
  orbits.card = 17794 ∧
    orbitCount 1 = 2 ∧
    orbitCount 8 = 2 ∧
    orbitCount 24 = 8 ∧
    orbitCount 28 = 3 ∧
    orbitCount 42 = 1 ∧
    orbitCount 56 = 2 ∧
    orbitCount 63 = 2 ∧
    orbitCount 72 = 4 ∧
    orbitCount 84 = 8 ∧
    orbitCount 126 = 9 ∧
    orbitCount 168 = 52 ∧
    orbitCount 252 = 71 ∧
    orbitCount 336 = 153 ∧
    orbitCount 504 = 1826 ∧
    orbitCount 1008 = 15651

end MathlibPlus.Open.Combinatorics.BatchSemidirectOrbits
