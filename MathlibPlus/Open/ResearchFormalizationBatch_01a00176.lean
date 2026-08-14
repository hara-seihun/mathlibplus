import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a00176

noncomputable section

/-! The three-arm spider is represented on the explicitly numbered vertices
`0, ..., r+s+t`.  Vertex `0` is the centre and each arm occupies its own
consecutive interval. -/
def armEdge (start length i j : ℕ) : Prop :=
  (i = 0 ∧ j = start + 1) ∨
    (j = 0 ∧ i = start + 1) ∨
      ∃ k : Fin length,
        1 ≤ k.val ∧
          ((i = start + k.val ∧ j = start + k.val + 1) ∨
            (j = start + k.val ∧ i = start + k.val + 1))

def spiderAdj (r s t : ℕ) (i j : Fin (1 + r + s + t)) : Prop :=
  armEdge 0 r i.val j.val ∨
    armEdge r s i.val j.val ∨
      armEdge (r + s) t i.val j.val

def spiderArms (r s t : ℕ) : Multiset ℕ := r ::ₘ s ::ₘ t ::ₘ 0

def spiderIso (r s t r' s' t' : ℕ) : Prop :=
  ∃ e : Fin (1 + r + s + t) ≃ Fin (1 + r' + s' + t'),
    ∀ (i j : Fin (1 + r + s + t)),
      spiderAdj r s t i j ↔ spiderAdj r' s' t' (e i) (e j)

def spiderDegree (r s t : ℕ) (i : Fin (1 + r + s + t)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => spiderAdj r s t i j)).card

def spiderLaplacian (r s t : ℕ) : Matrix (Fin (1 + r + s + t)) (Fin (1 + r + s + t)) ℤ := by
  classical
  exact fun i j =>
    if i = j then (spiderDegree r s t i : ℤ)
    else if spiderAdj r s t i j then -1 else 0

def spiderCharacteristic (r s t : ℕ) : Polynomial ℤ := by
  classical
  exact Matrix.det (fun i j =>
    if i = j then Polynomial.X - Polynomial.C (spiderDegree r s t i : ℤ)
    else if spiderAdj r s t i j then 1 else 0)

def continuantP : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C 2
  | n + 2 =>
      (Polynomial.X - Polynomial.C 2) * continuantP (n + 1) - continuantP n

def continuantQ : ℕ → Polynomial ℤ
  | 0 => 0
  | 1 => Polynomial.X - Polynomial.C 1
  | n + 2 =>
      (Polynomial.X - Polynomial.C 1) * continuantP (n + 1) - continuantP n

def continuantTau : ℕ → Polynomial ℤ
  | 0 => 0
  | 1 => 1
  | 2 => Polynomial.X - Polynomial.C 1
  | n + 3 =>
      (Polynomial.X - Polynomial.C 1) * continuantP (n + 1) - continuantP n

def Gamma := {q : ℚ // 0 < q}

instance : One Gamma := ⟨⟨1, by norm_num⟩⟩
instance : Mul Gamma := ⟨fun a b => ⟨a.1 * b.1, mul_pos a.2 b.2⟩⟩
instance : Inv Gamma := ⟨fun a => ⟨a.1⁻¹, inv_pos.mpr a.2⟩⟩

instance : Group Gamma where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc := by intro a b c; exact Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul := by intro a; exact Subtype.ext (one_mul a.1)
  mul_one := by intro a; exact Subtype.ext (mul_one a.1)
  inv_mul_cancel := by
    intro a
    apply Subtype.ext
    exact inv_mul_cancel₀ (ne_of_gt a.2)

abbrev ComplexGroupAlgebra := MonoidAlgebra ℂ Gamma

def groupUnitary (r : Gamma) : ComplexGroupAlgebra := MonoidAlgebra.single r 1

def trivialCharacter : Gamma →* ℂ :=
  { toFun := fun _ => 1
    map_one' := by simp
    map_mul' := by intro a b; simp }

def tau : ComplexGroupAlgebra →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ Gamma trivialCharacter

def shiftMap (c : ℝ) : C(ℝ, ℝ) :=
  { toFun := fun u => u + c
    continuous_toFun := continuous_id.add continuous_const }

abbrev CbReal := BoundedContinuousFunction ℝ ℝ

def translate (c : ℝ) (f : CbReal) : CbReal :=
  BoundedContinuousFunction.mk (f.toContinuousMap.comp (shiftMap c)) (by
    rcases f.bounded with ⟨C, hC⟩
    exact ⟨C, by intro x y; exact hC (x + c) (y + c)⟩)

def nonnegative (f : CbReal) : Prop := ∀ u : ℝ, 0 ≤ f u

def isMean (M : CbReal →ₗ[ℝ] ℝ) : Prop :=
  (∀ f, nonnegative f → 0 ≤ M f) ∧
    M (BoundedContinuousFunction.const ℝ 1) = 1 ∧
      ∀ (r : Gamma) (f : CbReal),
        M (translate (Real.log (r.1 : ℝ)) f) = M f

def kappaTwo (f : CbReal) : ℝ := f (Real.log 2) - f 0

def coboundaryTwo (M : CbReal →ₗ[ℝ] ℝ) (f : CbReal) : ℝ :=
  M (translate (Real.log 2) f - f)

def theta (t : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-Real.pi * (k : ℝ) ^ 2 * t)

def hTheta (u : ℝ) : ℝ := theta (Real.exp u) / (1 + theta (Real.exp u))

def kappaPlain (f : ℝ → ℝ) : ℝ := f (Real.log 2) - f 0

def claim58546 : Prop :=
  (∀ (r : Gamma) (a : ComplexGroupAlgebra),
      tau (groupUnitary r * a) = tau a ∧
        tau (groupUnitary r * a - a) = 0) ∧
    (∀ (M : CbReal →ₗ[ℝ] ℝ), isMean M →
      ∀ f : CbReal, coboundaryTwo M f = 0) ∧
    Continuous hTheta ∧
    (∃ C : ℝ, ∀ u v : ℝ, dist (hTheta u) (hTheta v) ≤ C) ∧
    StrictAnti hTheta ∧
    kappaPlain hTheta < 0 ∧
    ∀ (M : CbReal →ₗ[ℝ] ℝ), isMean M →
      (kappaTwo : CbReal → ℝ) ≠ coboundaryTwo M

def claim58555 : Prop :=
  ∀ b : ℕ, 2 ≤ b →
    Fintype.card (Fin (1 + 1 + 1 + 2 * b)) = 2 * b + 3 ∧
      Fintype.card (Fin (1 + 1 + b + (b + 1))) = 2 * b + 3 ∧
      Fintype.card (Fin (1 + 2 + b + b)) = 2 * b + 3 ∧
      spiderArms 1 1 (2 * b) ≠ spiderArms 1 b (b + 1) ∧
      spiderArms 1 1 (2 * b) ≠ spiderArms 2 b b ∧
      spiderArms 1 b (b + 1) ≠ spiderArms 2 b b ∧
      ¬ spiderIso 1 1 (2 * b) 1 b (b + 1) ∧
      ¬ spiderIso 1 1 (2 * b) 2 b b ∧
      ¬ spiderIso 1 b (b + 1) 2 b b

def claim58560 : Prop :=
  ∀ r s t : ℕ, 0 < r → 0 < s → 0 < t →
    spiderCharacteristic r s t =
      (Polynomial.X - Polynomial.C 3) * continuantQ r * continuantQ s * continuantQ t -
        continuantTau r * continuantQ s * continuantQ t -
        continuantQ r * continuantTau s * continuantQ t -
        continuantQ r * continuantQ s * continuantTau t

def claim58561 : Prop :=
  ∀ b : ℕ, 2 ≤ b →
    spiderCharacteristic 1 1 (2 * b) + spiderCharacteristic 2 b b =
        2 * spiderCharacteristic 1 b (b + 1) ∧
      (spiderCharacteristic 1 1 (2 * b) - spiderCharacteristic 1 b (b + 1)).coeff 2 =
        -((b : ℤ) * ((b : ℤ) - 1))

def claim58562 : Prop :=
  ∀ b : ℕ, 2 ≤ b →
    let delta := spiderCharacteristic 1 1 (2 * b) - spiderCharacteristic 1 b (b + 1)
    let defect :=
      spiderCharacteristic 1 1 (2 * b) * spiderCharacteristic 2 b b -
        spiderCharacteristic 1 b (b + 1) ^ 2
    defect = -delta ^ 2 ∧
      defect ≠ 0 ∧
      (∀ k : ℕ, k < 4 → defect.coeff k = 0) ∧
      defect.coeff 4 = -((b : ℤ) ^ 2 * ((b : ℤ) - 1) ^ 2) ∧
      defect.coeff 4 ≠ 0

abbrev F5 := ZMod 5
abbrev A5 := Fin 5 → F5
abbrev B5 := Fin 4 → F5
abbrev A5Dual := A5 →ₗ[F5] F5
abbrev H5 := A5 × B5

def dCoordinates : Fin 9 → B5 :=
  ![![1, 4, 0, 0],
    ![0, 1, 1, 0],
    ![1, 4, 2, 2],
    ![1, 3, 0, 4],
    ![1, 1, 3, 1],
    ![1, 3, 4, 3],
    ![1, 0, 3, 2],
    ![1, 4, 2, 1],
    ![1, 4, 3, 1]]

def uCoordinates : Fin 9 → (Fin 5 → F5) :=
  ![![0, 0, 0, 0, 2],
    ![1, 1, 4, 4, 1],
    ![1, 0, 3, 1, 3],
    ![4, 4, 2, 1, 1],
    ![2, 3, 4, 3, 4],
    ![1, 2, 2, 0, 3],
    ![0, 4, 2, 1, 0],
    ![4, 1, 2, 0, 2],
    ![3, 1, 0, 4, 0]]

def lambdaCoordinates : Fin 9 → F5 := ![1, 0, 0, 0, 0, 0, 0, 0, 0]

def covector (v : Fin 5 → F5) : A5Dual :=
  { toFun := fun x => ∑ j : Fin 5, v j * x j
    map_add' := by
      intro x y
      classical
      simp [Finset.sum_add_distrib, mul_add]
    map_smul' := by
      intro c x
      classical
      simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] }

def uData : Fin 9 → A5Dual := fun i => covector (uCoordinates i)

def dMatrix : Matrix (Fin 4) (Fin 9) F5 := fun i j => dCoordinates j i

def uMatrix : Matrix (Fin 5) (Fin 9) F5 := fun i j => uCoordinates j i

abbrev Tensor5 := TensorProduct F5 A5Dual B5

def tensorFamily : (Fin 9 → F5) →ₗ[F5] Tensor5 :=
  { toFun := fun c => ∑ i : Fin 9, c i • (uData i ⊗ₜ[F5] dCoordinates i)
    map_add' := by
      intro c d
      classical
      simp [Finset.sum_add_distrib, add_smul]
    map_smul' := by
      intro c d
      classical
      simp [Finset.smul_sum, smul_smul] }

def claim58565 : Prop :=
  Matrix.rank dMatrix = 4 ∧
    Matrix.rank uMatrix = 5 ∧
    uMatrix * dMatrix.transpose = 0 ∧
    Module.finrank F5 (LinearMap.range tensorFamily) = 8 ∧
    Module.finrank F5 (LinearMap.ker tensorFamily) = 1

def claim58566 : Prop :=
  Module.finrank F5 (LinearMap.range tensorFamily) = 8 ∧
    Module.finrank F5 (LinearMap.ker tensorFamily) = 1 ∧
    tensorFamily (fun _ => 1) = 0 ∧
    ∀ c : Fin 9 → F5,
      tensorFamily c = 0 ↔ ∃ a : F5, c = fun _ => a

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a00176
