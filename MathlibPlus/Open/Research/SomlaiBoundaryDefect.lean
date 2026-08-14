import Mathlib

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.Research.Somlai

abbrev SomlaiB (p : ℕ) := Fin (p + 1) → ZMod p
abbrev SomlaiV (p : ℕ) := Fin (p + 2) → ZMod p

inductive SomlaiLabel (p : ℕ) where
  | first (i : Fin (p + 1))
  | second (i : Fin (p + 1))
  | terminal
  deriving DecidableEq, Fintype

variable (p : ℕ) [Fact p.Prime]

noncomputable def coordinateB (i : Fin (p + 1)) : SomlaiB p :=
  fun j => if j = i then 1 else 0

noncomputable def coordinateV (j : Fin (p + 2)) : SomlaiV p :=
  fun k => if k = j then 1 else 0

noncomputable def sumB : SomlaiB p :=
  ∑ i : Fin (p + 1), coordinateB p i

noncomputable def sumV : SomlaiV p :=
  ∑ j : Fin (p + 2), coordinateV p j

noncomputable def somlaiDirection : SomlaiLabel p → SomlaiB p
  | .first i => coordinateB p i
  | .second i => sumB p - coordinateB p i
  | .terminal => sumB p

noncomputable def somlaiCoefficient : SomlaiLabel p → SomlaiV p
  | .first i => coordinateV p 0 + coordinateV p i.succ
  | .second i => coordinateV p i.succ + sumV p
  | .terminal => sumV p

noncomputable def coefficientLine (L : SomlaiLabel p) : Submodule (ZMod p) (SomlaiV p) :=
  (ZMod p) ∙ somlaiCoefficient p L

abbrev GroupAlgebra := MonoidAlgebra (ZMod p) (Multiplicative (SomlaiB p))
abbrev Ambient := SomlaiV p ⊗[ZMod p] GroupAlgebra p

noncomputable def tau (x : SomlaiB p) : GroupAlgebra p :=
  MonoidAlgebra.single (Multiplicative.ofAdd x) 1

noncomputable def augmentation : GroupAlgebra p →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) (Multiplicative (SomlaiB p))
    { toFun := fun _ => 1
      map_one' := rfl
      map_mul' := by intro x y; simp }

noncomputable def augmentationIdeal : Ideal (GroupAlgebra p) :=
  RingHom.ker (augmentation p).toRingHom

noncomputable def coefficientMap : GroupAlgebra p →ₗ[ZMod p]
    (Multiplicative (SomlaiB p) →₀ ZMod p) :=
  { toFun := fun a => a.coeff
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

noncomputable def moment : GroupAlgebra p →ₗ[ZMod p] SomlaiB p :=
  (Finsupp.linearCombination (ZMod p)
    (fun x : Multiplicative (SomlaiB p) => Multiplicative.toAdd x)).comp
      (coefficientMap p)

noncomputable def firstMoment : Ambient p →ₗ[ZMod p]
    (SomlaiV p ⊗[ZMod p] SomlaiB p) :=
  LinearMap.lTensor (SomlaiV p) (moment p)

noncomputable def relationGenerators : Set (Ambient p) :=
  {z | ∃ L : SomlaiLabel p, ∃ u : SomlaiV p,
      u ∈ coefficientLine p L ∧ ∃ r : GroupAlgebra p,
        z = u ⊗ₜ[ZMod p]
          ((tau p (somlaiDirection p L) - 1) * r)}

noncomputable def relationModule : Submodule (ZMod p) (Ambient p) :=
  Submodule.span (ZMod p) (relationGenerators p)

noncomputable def augmentationProductGenerators : Set (Ambient p) :=
  {z | ∃ L : SomlaiLabel p, ∃ u : SomlaiV p,
      u ∈ coefficientLine p L ∧ ∃ i : GroupAlgebra p,
      i ∈ augmentationIdeal p ∧ ∃ r : GroupAlgebra p,
        z = u ⊗ₜ[ZMod p]
          ((tau p (somlaiDirection p L) - 1) * (i * r))}

noncomputable def augmentationProduct : Submodule (ZMod p) (Ambient p) :=
  Submodule.span (ZMod p) (augmentationProductGenerators p)

noncomputable def momentKernelInC : Submodule (ZMod p) (Ambient p) :=
  relationModule p ⊓ (firstMoment p).ker

noncomputable def augmentationProductInKernel :
    Submodule (ZMod p) (momentKernelInC p) :=
  Submodule.comap (momentKernelInC p).subtype (augmentationProduct p)

noncomputable def boundaryDefect : ℕ :=
  Module.finrank (ZMod p)
    (momentKernelInC p ⧸ augmentationProductInKernel p)

/-- The explicit Somlai profile has a one-dimensional first-moment boundary defect. -/
def somlai_boundary_defect_one : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), p % 2 = 1 →
    @boundaryDefect p ⟨hp⟩ = 1

end MathlibPlus.Open.Research.Somlai
