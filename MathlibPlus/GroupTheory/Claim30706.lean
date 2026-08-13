import Mathlib

namespace MathlibPlus.GroupTheory

/-- A central elementary Sylow subgroup has a `p'` complement, and the
complement commutes with it, giving an internal direct-product decomposition. -/
theorem centralElementarySylow_directProduct_claim30706
    {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Sylow p G)
    (hcentral : (A : Subgroup G) ≤ Subgroup.center G)
    (helementary : ∀ a : A, a ^ p = 1) :
    ∃ J : Subgroup G,
      (A : Subgroup G).IsComplement' J ∧
      Nat.Coprime (Nat.card J) p ∧
      (∃ e : A × J ≃* G,
        ∀ (a : A) (j : J), e (a, j) = (a : G) * j) := by
  letI : (A : Subgroup G).Normal :=
    ⟨fun n hn g => by
      have hcomm : g * n = n * g :=
        Subgroup.mem_center_iff.mp (hcentral hn) g
      rw [hcomm]
      simpa using hn⟩
  obtain ⟨J, hJ⟩ :=
    Subgroup.exists_right_complement'_of_coprime A.card_coprime_index
  have hindex : (A : Subgroup G).index = Nat.card J :=
    hJ.symm.index_eq_card
  have hnot : ¬p ∣ Nat.card J := by
    rw [← hindex]
    exact A.not_dvd_index
  have hcop : Nat.Coprime (Nat.card J) p :=
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr hnot).symm
  have hcommute : ∀ (a : A) (j : J), (a : G) * j = j * a := by
    intro a j
    exact (Subgroup.mem_center_iff.mp (hcentral a.property) j).symm
  let f : A × J →* G :=
    { toFun := fun x => (x.1 : G) * x.2
      map_one' := by simp
      map_mul' := by
        intro x y
        calc
          ((x.1 * y.1 : A) : G) * (x.2 * y.2 : J) =
              (x.1 : G) * (y.1 : G) * (x.2 : G) * (y.2 : G) := by
                simp only [Subgroup.coe_mul, mul_assoc]
          _ = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by
                simp only [mul_assoc]
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
                rw [hcommute y.1 x.2]
          _ = ((x.1 : G) * x.2) * ((y.1 : G) * y.2) := by
                simp only [mul_assoc] }
  have hf : Function.Bijective f := by
    exact (Subgroup.isComplement_iff_bijective (A : Subgroup G) J).mp hJ
  let e : A × J ≃* G := MulEquiv.ofBijective f hf
  refine ⟨J, hJ, hcop, e, ?_⟩
  intro a j
  rfl

end MathlibPlus.GroupTheory
