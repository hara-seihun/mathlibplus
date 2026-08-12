import Mathlib

namespace MathlibPlus.GroupTheory

/--
Claim 40025. Conjugating source and target copies by independent elements transports
any conjugator of their canonical copies.
-/
theorem conjugateCopies_transport_claim40025
    {G : Type*} [Group G]
    (R_U R_V R S : Subgroup G) (p q sigma0 : G)
    (hR : R = Subgroup.map (MulAut.conj p) R_U)
    (hS : S = Subgroup.map (MulAut.conj q) R_V)
    (hσ : R_V = Subgroup.map (MulAut.conj sigma0) R_U) :
    S = Subgroup.map (MulAut.conj (q * sigma0 * p⁻¹)) R := by
  rw [hR, hS, hσ]
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  simp [mul_assoc]

end MathlibPlus.GroupTheory
