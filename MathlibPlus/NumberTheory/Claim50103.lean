import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory.Claim50103

noncomputable section

open Polynomial

/-- Every odd prime field has a monic reciprocal irreducible quadratic. -/
theorem existsIrreducibleReciprocalQuadratic_claim50103
    (q : ℕ) (hq : Nat.Prime q) (hodd : q % 2 = 1) :
    ∃ a : ZMod q,
      Irreducible (X ^ 2 - C a * X + 1) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let p : ZMod q → Polynomial (ZMod q) :=
    fun a => C (1 : ZMod q) * X ^ 2 + C (-a) * X + C (1 : ZMod q)
  have hp (a : ZMod q) : p a = X ^ 2 - C a * X + 1 := by
    dsimp [p]
    simp only [map_neg, map_one, sub_eq_add_neg, neg_mul]
    ring
  have hmonic (a : ZMod q) : (p a).Monic := by
    dsimp [p]
    apply monic_of_degree_le 2 degree_quadratic_le
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hnd (a : ZMod q) : (p a).natDegree = 2 := by
    dsimp [p]
    exact natDegree_quadratic one_ne_zero
  let f : {x : ZMod q // x ≠ 0} → ZMod q :=
    fun x => -((x : ZMod q) + (x : ZMod q)⁻¹)
  have hcard : Fintype.card {x : ZMod q // x ≠ 0} = q - 1 := by
    have hc := Fintype.card_subtype_compl (fun x : ZMod q => x = 0)
    simpa [ZMod.card] using hc
  have hex : ∃ a : ZMod q, Irreducible (p a) := by
    by_contra h
    push_neg at h
    have hsurj : Function.Surjective f := by
      intro a
      have hni : ¬Irreducible (p a) := h a
      obtain ⟨c₁, c₂, hc₀, hc₁⟩ :=
        ((hmonic a).not_irreducible_iff_exists_add_mul_eq_coeff (hnd a)).mp hni
      have hc₀' : (1 : ZMod q) = c₁ * c₂ := by
        simpa [p, Polynomial.coeff_add, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X,
          Polynomial.coeff_one] using hc₀
      have hc₁' : -a = c₁ + c₂ := by
        have hc₁'' := hc₁
        simp only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at hc₁''
        norm_num at hc₁''
        exact hc₁''
      have hc₁_ne : c₁ ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at hc₀'
        exact one_ne_zero hc₀'
      have hc₂ : c₂ = c₁⁻¹ := eq_inv_of_mul_eq_one_right hc₀'.symm
      refine ⟨⟨c₁, hc₁_ne⟩, ?_⟩
      dsimp [f]
      calc
        - (c₁ + c₁⁻¹) = -(c₁ + c₂) := by rw [hc₂]
        _ = a := by rw [← hc₁']; simp
    have hcardle := Fintype.card_le_of_surjective f hsurj
    rw [ZMod.card, hcard] at hcardle
    have hqpos : 0 < q := hq.pos
    omega
  rcases hex with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [← hp a]
  exact ha

end
end MathlibPlus.NumberTheory.Claim50103
