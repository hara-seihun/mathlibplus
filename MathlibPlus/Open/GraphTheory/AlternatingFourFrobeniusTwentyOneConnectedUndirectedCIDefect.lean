-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

namespace MathlibPlus.Open.GraphTheory

private def f21AddScaleTwo : ZMod 7 ≃+ ZMod 7 :=
  { toFun := fun x => 2 * x
    invFun := fun x => 4 * x
    left_inv := by intro x; native_decide +revert
    right_inv := by intro x; native_decide +revert
    map_add' := by intro x y; ring }

private def f21MulScaleTwo : MulAut (Multiplicative (ZMod 7)) :=
  AddEquiv.toMultiplicative f21AddScaleTwo

private def f21Action : Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 7)) where
  toFun z := f21MulScaleTwo ^ (ZMod.val z)
  map_one' := by
    ext z
    change (f21MulScaleTwo ^ 0) z = z
    simp
  map_mul' x y := by
    ext z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> native_decide

private abbrev f21Group :=
  SemidirectProduct (Multiplicative (ZMod 7)) (Multiplicative (ZMod 3)) f21Action

private instance : Fintype f21Group where
  elems := Finset.univ.image (fun x : Multiplicative (ZMod 7) × Multiplicative (ZMod 3) =>
    (⟨x.1, x.2⟩ : f21Group))
  complete := by
    intro x
    rw [Finset.mem_image]
    refine ⟨(x.left, x.right), Finset.mem_univ _, ?_⟩
    rfl

/--
The fixed order-252 connected ordinary Cayley CI defect discovered from the
nonabelian order-21 orientation tags.  The order-21 factor is the explicit
semidirect product in which the quotient generator acts on `ZMod 7` by
multiplication by `2`; the conclusion retains the generating, inverse-closed,
identity-free, normalized involution, incidence, and non-automorphism clauses.
-/
def alternatingFourFrobeniusTwentyOneConnectedUndirectedCIDefect : Prop :=
  let G := f21Group × alternatingGroup (Fin 4)
  ∃ (S T : Set G) (Q : G ≃ G),
    Q 1 = 1 ∧
    (∀ x : G, Q (Q x) = x) ∧
    Set.ncard S = 12 ∧
    Set.ncard T = 12 ∧
    Subgroup.closure S = ⊤ ∧
    Subgroup.closure T = ⊤ ∧
    (∀ x : G, x ∈ S → x⁻¹ ∈ S) ∧
    (∀ x : G, x ∈ T → x⁻¹ ∈ T) ∧
    1 ∉ S ∧
    1 ∉ T ∧
    (∀ x y : G,
      x⁻¹ * y ∈ S ↔ (Q x)⁻¹ * Q y ∈ T) ∧
    (∀ α : G ≃* G, α '' S ≠ T)

end MathlibPlus.Open.GraphTheory
