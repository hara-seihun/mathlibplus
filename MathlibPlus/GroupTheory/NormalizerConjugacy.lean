import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory

/-- Conjugacy of two subgroups whose common derived subgroup is `P` already
lies in the normalizer of `P`. The regular-action hypotheses from R-1133 are
not needed for this exact group-theoretic core. -/
theorem claim30073_normalizerConjugacy
    {K : Type*} [Group K]
    (P H₁ H₂ : Subgroup K) (x : K)
    (h₁ : P = ⁅H₁, H₁⁆)
    (h₂ : P = ⁅H₂, H₂⁆)
    (hx : Subgroup.map (MulAut.conj x).toMonoidHom H₁ = H₂) :
    x ∈ Subgroup.normalizer (P : Set K) := by
  have hPmap : Subgroup.map (MulAut.conj x).toMonoidHom P = P := by
    calc
      Subgroup.map (MulAut.conj x).toMonoidHom P =
          Subgroup.map (MulAut.conj x).toMonoidHom ⁅H₁, H₁⁆ := by rw [h₁]
      _ = ⁅Subgroup.map (MulAut.conj x).toMonoidHom H₁,
          Subgroup.map (MulAut.conj x).toMonoidHom H₁⁆ :=
        Subgroup.map_commutator H₁ H₁ (MulAut.conj x).toMonoidHom
      _ = ⁅H₂, H₂⁆ := by rw [hx]
      _ = P := h₂.symm
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have hmap : (MulAut.conj x) k ∈
        Subgroup.map (MulAut.conj x).toMonoidHom P := by
      exact Subgroup.mem_map_of_mem _ hk
    rw [hPmap] at hmap
    simpa [MulAut.conj_apply] using hmap
  · intro hk
    have hmap : (MulAut.conj x) k ∈
        Subgroup.map (MulAut.conj x).toMonoidHom P := by
      rw [hPmap]
      exact hk
    have hinv := (Subgroup.mem_map_equiv (f := MulAut.conj x) (K := P)
      (x := (MulAut.conj x) k)).mp hmap
    simpa [MulAut.conj_apply, mul_assoc] using hinv

end MathlibPlus.GroupTheory
