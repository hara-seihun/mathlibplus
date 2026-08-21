-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.GraphTheory.A4TwoRelationMinimumClassification

private abbrev A4MinimumClassificationGroup := alternatingGroup (Fin 4)
private def a4mc_p0 : A4MinimumClassificationGroup :=
  ⟨1, by change Equiv.Perm.sign 1 = 1; native_decide⟩
private def a4mc_p1 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (1 : Fin 4) 2) * Equiv.swap 2 3, by
    change Equiv.Perm.sign ((Equiv.swap (1 : Fin 4) 2) * Equiv.swap 2 3) = 1
    native_decide⟩
private def a4mc_p2 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (1 : Fin 4) 2) * Equiv.swap 1 3, by
    change Equiv.Perm.sign ((Equiv.swap (1 : Fin 4) 2) * Equiv.swap 1 3) = 1
    native_decide⟩
private def a4mc_p3 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 1) * Equiv.swap 2 3, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 1) * Equiv.swap 2 3) = 1
    native_decide⟩
private def a4mc_p4 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 2, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 2) = 1
    native_decide⟩
private def a4mc_p5 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 3, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 3) = 1
    native_decide⟩
private def a4mc_p6 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 2) * Equiv.swap 1 2, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 2) * Equiv.swap 1 2) = 1
    native_decide⟩
private def a4mc_p7 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 2) * Equiv.swap 2 3, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 2) * Equiv.swap 2 3) = 1
    native_decide⟩
private def a4mc_p8 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 2) * Equiv.swap 1 3, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 2) * Equiv.swap 1 3) = 1
    native_decide⟩
private def a4mc_p9 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 3) * Equiv.swap 1 3, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 3) * Equiv.swap 1 3) = 1
    native_decide⟩
private def a4mc_p10 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 3) * Equiv.swap 2 3, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 3) * Equiv.swap 2 3) = 1
    native_decide⟩
private def a4mc_p11 : A4MinimumClassificationGroup :=
  ⟨(Equiv.swap (0 : Fin 4) 3) * Equiv.swap 1 2, by
    change Equiv.Perm.sign ((Equiv.swap (0 : Fin 4) 3) * Equiv.swap 1 2) = 1
    native_decide⟩

private def a4mc_qfun (x : A4MinimumClassificationGroup) : A4MinimumClassificationGroup :=
  if x = a4mc_p0 then a4mc_p0 else
  if x = a4mc_p1 then a4mc_p1 else
  if x = a4mc_p2 then a4mc_p2 else
  if x = a4mc_p3 then a4mc_p3 else
  if x = a4mc_p4 then a4mc_p7 else
  if x = a4mc_p5 then a4mc_p10 else
  if x = a4mc_p6 then a4mc_p6 else
  if x = a4mc_p7 then a4mc_p4 else
  if x = a4mc_p8 then a4mc_p11 else
  if x = a4mc_p9 then a4mc_p9 else
  if x = a4mc_p10 then a4mc_p5 else a4mc_p8

private theorem a4mc_q_involutive : ∀ x : A4MinimumClassificationGroup,
    a4mc_qfun (a4mc_qfun x) = x := by
  native_decide

private def a4mc_q : A4MinimumClassificationGroup ≃ A4MinimumClassificationGroup :=
  { toFun := a4mc_qfun
    invFun := a4mc_qfun
    left_inv := a4mc_q_involutive
    right_inv := a4mc_q_involutive }

private def a4mc_source : Fin 2 → Set A4MinimumClassificationGroup :=
  ![{a4mc_p2, a4mc_p3, a4mc_p4, a4mc_p7, a4mc_p9}, {a4mc_p8}]

private def a4mc_target : Fin 2 → Set A4MinimumClassificationGroup :=
  ![{a4mc_p2, a4mc_p3, a4mc_p4, a4mc_p7, a4mc_p9}, {a4mc_p11}]

private def a4mc_inverse_family (U : Fin 2 → Set A4MinimumClassificationGroup)
    (i : Fin 2) : Set A4MinimumClassificationGroup :=
  {x | x⁻¹ ∈ U i}

private def a4mc_transformed_family (a : A4MinimumClassificationGroup ≃* A4MinimumClassificationGroup)
    (U : Fin 2 → Set A4MinimumClassificationGroup) (σ : Equiv.Perm (Fin 2))
    (r : Bool) : Fin 2 → Set A4MinimumClassificationGroup :=
  fun i => a '' (if r then a4mc_inverse_family U (σ i) else U (σ i))

private def a4mc_is_defect (S T : Fin 2 → Set A4MinimumClassificationGroup)
    (e : A4MinimumClassificationGroup ≃ A4MinimumClassificationGroup) : Prop :=
  e 1 = 1 ∧
  (∀ i, 1 ∉ S i ∧ 1 ∉ T i) ∧
  (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) ∧
  (∀ a : A4MinimumClassificationGroup ≃* A4MinimumClassificationGroup,
    ¬ (∀ i, a '' S i = T i))

private noncomputable def a4mc_total_valency (S : Fin 2 → Set A4MinimumClassificationGroup) : ℕ :=
  Set.ncard (S 0) + Set.ncard (S 1)

private def a4mc_rep_properties : Prop :=
  a4mc_is_defect a4mc_source a4mc_target a4mc_q ∧
  (∀ x : A4MinimumClassificationGroup, a4mc_q (a4mc_q x) = x) ∧
  Set.ncard (a4mc_source 0) = 5 ∧ Set.ncard (a4mc_source 1) = 1 ∧
  Set.ncard (a4mc_target 0) = 5 ∧ Set.ncard (a4mc_target 1) = 1 ∧
  Disjoint (a4mc_source 0) (a4mc_source 1) ∧
  Disjoint (a4mc_target 0) (a4mc_target 1) ∧
  (∃ a : A4MinimumClassificationGroup ≃* A4MinimumClassificationGroup, a '' a4mc_source 0 = a4mc_target 0) ∧
  (∃ a : A4MinimumClassificationGroup ≃* A4MinimumClassificationGroup, a '' a4mc_source 1 = a4mc_target 1)

end MathlibPlus.GraphTheory.A4TwoRelationMinimumClassification

namespace MathlibPlus.GraphTheory.A4TwoRelationMinimumClassification

/-- The minimum total valency and equality classification for simultaneous
ordered pairs of directed right-Cayley relations on `A₄`. -/
def _root_.MathlibPlus.Open.GraphTheory.alternatingFourTwoRelationMinimumClassification : Prop :=
  a4mc_rep_properties ∧
  ∀ (S T : Fin 2 → Set A4MinimumClassificationGroup)
      (e : A4MinimumClassificationGroup ≃ A4MinimumClassificationGroup),
    a4mc_is_defect S T e →
      a4mc_total_valency S ≥ 6 ∧
      (a4mc_total_valency S = 6 →
        ∃ (a b : A4MinimumClassificationGroup ≃* A4MinimumClassificationGroup)
          (σ : Equiv.Perm (Fin 2)) (r : Bool),
          (∀ i, S i = a4mc_transformed_family a a4mc_source σ r i) ∧
          (∀ i, T i = a4mc_transformed_family b a4mc_target σ r i))

end MathlibPlus.GraphTheory.A4TwoRelationMinimumClassification
