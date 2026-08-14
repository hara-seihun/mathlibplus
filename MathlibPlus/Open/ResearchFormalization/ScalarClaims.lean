import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ScalarClaims

local instance fact13 : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance fact3 : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev V13 := ZMod 13 × ZMod 13
abbrev K13 := Multiplicative V13
abbrev Q3 := Multiplicative (ZMod 3)

def scalarAddEquiv (a : ZMod 13) (ha : a ≠ 0) : V13 ≃+ V13 :=
  { toFun := fun v => (a * v.1, a * v.2)
    invFun := fun v => (a⁻¹ * v.1, a⁻¹ * v.2)
    left_inv := by
      intro v
      ext <;> dsimp <;>
        rw [← mul_assoc, inv_mul_cancel₀ (a := a) ha, one_mul]
    right_inv := by
      intro v
      ext <;> dsimp <;>
        rw [← mul_assoc, mul_inv_cancel₀ (a := a) ha, one_mul]
    map_add' := by
      intro v w
      ext <;> simp [mul_add] }

def scalarMulAut (a : ZMod 13) (ha : a ≠ 0) : MulAut K13 :=
  (scalarAddEquiv a ha).toMultiplicative

def θ : ZMod 13 := 3

def θScalar (i : Q3) : ZMod 13 := θ ^ i.val

theorem θScalar_ne_zero (i : Q3) : θScalar i ≠ 0 := by
  have h : (3 : ZMod 13) ≠ 0 := by decide
  exact pow_ne_zero _ h

def scalarActionAt (i : Q3) : MulAut K13 :=
  scalarMulAut (θScalar i) (θScalar_ne_zero i)

def scalarAction : Q3 →* MulAut K13 :=
  { toFun := scalarActionAt
    map_one' := by native_decide
    map_mul' := by native_decide }

abbrev ScalarG := K13 ⋊[scalarAction] Q3

def scalarGEquivProduct : ScalarG ≃ K13 × Q3 :=
  { toFun := fun x => (x.left, x.right)
    invFun := fun x => SemidirectProduct.mk x.1 x.2
    left_inv := by intro x; cases x; rfl
    right_inv := by intro x; rfl }

local instance : Fintype ScalarG := Fintype.ofEquiv (K13 × Q3) scalarGEquivProduct.symm

def scalarSemidirectElement (v : V13) (i : Q3) : ScalarG :=
  SemidirectProduct.mk (Multiplicative.ofAdd v) i

def scalarSemidirectMultiplication : Prop :=
  ∀ (v w : V13) (i j : Q3),
    scalarSemidirectElement v i * scalarSemidirectElement w j =
      scalarSemidirectElement (v + θScalar i • w) (i * j)

def scalarKernel : Subgroup ScalarG :=
  Subgroup.map (SemidirectProduct.inl : K13 →* ScalarG) ⊤

def scalarKernelUniqueSylow : Prop :=
  letI : Fintype ScalarG := Fintype.ofFinite ScalarG
  letI : Fintype (Sylow 13 ScalarG) := Fintype.ofFinite (Sylow 13 ScalarG)
  Fintype.card (Sylow 13 ScalarG) = 1 ∧
    ∃ P : Sylow 13 ScalarG, P.toSubgroup = scalarKernel

def scalarQuotientReversalImpossible : Prop :=
  ¬ ∃ φ : MulAut ScalarG,
    ∀ x : ScalarG,
      SemidirectProduct.rightHom (φ x) = (SemidirectProduct.rightHom x)⁻¹

def scalarAutomorphismFormula : Prop :=
  ∀ φ : MulAut ScalarG,
    ∃ A : V13 ≃ₗ[ZMod 13] V13, ∃ d : V13, ∀ v : V13,
      φ (scalarSemidirectElement v (Multiplicative.ofAdd 0)) =
          scalarSemidirectElement (A v) (Multiplicative.ofAdd 0) ∧
      φ (scalarSemidirectElement v (Multiplicative.ofAdd 1)) =
          scalarSemidirectElement (A v + d) (Multiplicative.ofAdd 1) ∧
      φ (scalarSemidirectElement v (Multiplicative.ofAdd 2)) =
          scalarSemidirectElement (A v + (1 + θ) • d) (Multiplicative.ofAdd 2)

def claim_38759 : Prop :=
  letI : Fintype ScalarG := Fintype.ofFinite ScalarG
  letI : Fintype (MulAut ScalarG) := Fintype.ofFinite (MulAut ScalarG)
  θ = 3 ∧ θ⁻¹ = 9 ∧ θ ^ 3 = 1 ∧ 1 + θ + θ ^ 2 = 0 ∧
    scalarSemidirectMultiplication ∧ scalarKernelUniqueSylow ∧
    scalarQuotientReversalImpossible ∧ scalarAutomorphismFormula ∧
    Fintype.card (MulAut ScalarG) = 4429152

end MathlibPlus.Open.ResearchFormalization.ScalarClaims
