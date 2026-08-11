import Mathlib

/-!
# Sharp quiet-span voltage falsifier (claim 38645)

The abstract finite voltage model is made explicit over `ZMod 3`.  The
functional obstruction is kernel-checked and does not claim that this model
comes from a regular pair.
-/

namespace MathlibPlus.LinearAlgebra.Claim38645

abbrev Scalar := ZMod 3
abbrev Voltage := Scalar × Scalar
abbrev FreeVoltage := Voltage →₀ Scalar

def quietSet : Set Voltage := Set.univ

def q (x : Voltage) : Voltage := x

def affineAction (x : Voltage) : Voltage := x

def potential (x : Voltage) : Scalar := 0

def defect (x : Voltage) : Scalar := x.1 ^ 2

noncomputable def evaluation : FreeVoltage →ₗ[Scalar] Voltage :=
  Finsupp.lsum Scalar (fun x : Voltage => LinearMap.toSpanSingleton Scalar Voltage x)

noncomputable def relation : FreeVoltage :=
  Finsupp.single ((1 : Scalar), (0 : Scalar)) 1 +
    Finsupp.single ((2 : Scalar), (0 : Scalar)) 1

theorem quietSet_eq_univ : quietSet = (Set.univ : Set Voltage) := rfl

theorem quietSet_spans : Submodule.span Scalar quietSet = ⊤ := by
  simp [quietSet]

theorem zero_potential_on_quiet : ∀ x ∈ quietSet, potential x = 0 := by
  simp [quietSet, potential]

theorem component_preservation : ∀ x : Voltage, affineAction (q x) = x := by
  intro x
  rfl

theorem relation_mem_evaluation_kernel : relation ∈ LinearMap.ker evaluation := by
  change evaluation relation = 0
  rw [relation, map_add]
  simp [evaluation]
  decide

theorem relation_defect :
    defect ((1 : Scalar), (0 : Scalar)) + defect ((2 : Scalar), (0 : Scalar)) = 2 := by
  decide

theorem relation_defect_ne_zero :
    defect ((1 : Scalar), (0 : Scalar)) + defect ((2 : Scalar), (0 : Scalar)) ≠ 0 := by
  decide

theorem no_linear_extension_with_kernel_relation :
    ¬ ∃ L : FreeVoltage →ₗ[Scalar] Scalar,
      (∀ x : Voltage, L (Finsupp.single x 1) = defect x) ∧
        L relation = 0 := by
  rintro ⟨L, hL, hkernel⟩
  have hvalue : L relation =
      defect ((1 : Scalar), (0 : Scalar)) + defect ((2 : Scalar), (0 : Scalar)) := by
    rw [relation, map_add, hL, hL]
  rw [hkernel] at hvalue
  rw [relation_defect] at hvalue
  exact (by decide : ¬ ((0 : Scalar) = 2)) hvalue

end MathlibPlus.LinearAlgebra.Claim38645
