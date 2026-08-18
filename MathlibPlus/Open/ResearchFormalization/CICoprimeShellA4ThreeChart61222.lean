import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

private abbrev A4_61222 := alternatingGroup (Fin 4)

private def a4Word_61222 (h : A4_61222) : List (Fin 4) :=
  [h.1 0, h.1 1, h.1 2, h.1 3]

private def a4LexIndex_61222 (ι : A4_61222 ≃ Fin 12) : Prop :=
  ι 1 = 0 ∧ ∀ h k, ι h ≤ ι k ↔ a4Word_61222 h ≤ a4Word_61222 k

private def qI_61222 : Fin 12 → Fin 12 :=
  fun i => i

private def qR_61222 : Fin 12 → Fin 12
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 7
  | ⟨5, _⟩ => 10
  | ⟨6, _⟩ => 6
  | ⟨7, _⟩ => 4
  | ⟨8, _⟩ => 11
  | ⟨9, _⟩ => 9
  | ⟨10, _⟩ => 5
  | ⟨11, _⟩ => 8

private def qD_61222 : Fin 12 → Fin 12
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 5
  | ⟨6, _⟩ => 6
  | ⟨7, _⟩ => 9
  | ⟨8, _⟩ => 8
  | ⟨9, _⟩ => 7
  | ⟨10, _⟩ => 10
  | ⟨11, _⟩ => 11

private def beta_61222 : Fin 12 → Fin 12
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 4
  | ⟨6, _⟩ => 9
  | ⟨7, _⟩ => 10
  | ⟨8, _⟩ => 11
  | ⟨9, _⟩ => 6
  | ⟨10, _⟩ => 7
  | ⟨11, _⟩ => 8

private def chartArray_61222 (c : Fin 3) : Fin 12 → Fin 12 :=
  match c.val with
  | 0 => qI_61222
  | 1 => qR_61222
  | 2 => qD_61222
  | _ => qI_61222

private def chartMap_61222 (ι : A4_61222 ≃ Fin 12) (c : Fin 3) :
    A4_61222 → A4_61222 :=
  fun h => ι.symm (chartArray_61222 c (ι h))

private def fibreMap_61222 {A : Type*} [AddCommGroup A]
    (ι : A4_61222 ≃ Fin 12) (eta : Multiplicative A → Fin 3) :
    Multiplicative A × A4_61222 → Multiplicative A × A4_61222 :=
  fun x => (x.1, chartMap_61222 ι (eta x.1) x.2)

private def baseNeg_61222 {A : Type*} [AddGroup A]
    (a : Multiplicative A) : Multiplicative A :=
  Multiplicative.ofAdd (-a.toAdd)

private def rightCayleyAdj_61222 {G : Type*} [Group G]
    (S : Set G) (x y : G) : Prop :=
  x⁻¹ * y ∈ S

private def identityFreeInverseClosed_61222 {G : Type*} [Group G]
    (S : Set G) : Prop :=
  (1 : G) ∉ S ∧ ∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S

private def pointedCayleyIsomorphism_61222 {G : Type*} [Group G]
    (f : G → G) (S T : Set G) : Prop :=
  ∀ x y, rightCayleyAdj_61222 S x y ↔ rightCayleyAdj_61222 T (f x) (f y)

/-- Claim 61222: the three displayed opposite-orientation charts on the
lexicographically indexed twelve-point alternating group are sterile over
an arbitrary finite abelian base, uniformly for every finite relation tuple. -/
def claim61222_threeChartUnanchoredSterility : Prop :=
  ∀ (ι : A4_61222 ≃ Fin 12),
    a4LexIndex_61222 ι →
      ∀ (A : Type*) [AddCommGroup A] [Fintype A]
        (J : Type*) [Fintype J]
        (eta : Multiplicative A → Fin 3)
        (S T : J → Set (Multiplicative A × A4_61222)),
        Function.Bijective (fibreMap_61222 ι eta) →
        (∀ j, identityFreeInverseClosed_61222 (S j) ∧
          identityFreeInverseClosed_61222 (T j)) →
        (∀ j, pointedCayleyIsomorphism_61222
          (fibreMap_61222 ι eta) (S j) (T j)) →
        ((¬ ∀ a, eta a = (1 : Fin 3)) → ∀ j, S j = T j) ∧
        ((∀ a, eta a = (1 : Fin 3)) →
          ∃ beta : A4_61222 ≃* A4_61222,
            (∀ h, ι (beta h) = beta_61222 (ι h)) ∧
            ∃ alpha : (Multiplicative A × A4_61222) ≃*
                (Multiplicative A × A4_61222),
              (∀ a h, alpha (a, h) = (baseNeg_61222 a, beta h)) ∧
              ∀ j, alpha '' S j = T j)

end MathlibPlus.Open.ResearchFormalization
